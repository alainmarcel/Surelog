/*
 Copyright 2019 Alain Dargelas

 Licensed under the Apache License, Version 2.0 (the "License");
 you may not use this file except in compliance with the License.
 You may obtain a copy of the License at

 http://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software
 distributed under the License is distributed on an "AS IS" BASIS,
 WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 See the License for the specific language governing permissions and
 limitations under the License.
 */

/*
 * File:   CompileHelper.cpp
 * Author: alain
 *
 * Created on May 14, 2019, 8:03 PM
 */

#include "Surelog/DesignCompile/CompileHelper.h"

#include "Surelog/CommandLine/CommandLineParser.h"
#include "Surelog/Common/FileSystem.h"
#include "Surelog/Common/NodeId.h"
#include "Surelog/Common/PathId.h"
#include "Surelog/Design/DataType.h"
#include "Surelog/Design/DesignComponent.h"
#include "Surelog/Design/DummyType.h"
#include "Surelog/Design/Enum.h"
#include "Surelog/Design/FileCNodeId.h"
#include "Surelog/Design/FileContent.h"
#include "Surelog/Design/Function.h"
#include "Surelog/Design/LetStmt.h"
#include "Surelog/Design/ModuleDefinition.h"
#include "Surelog/Design/ModuleInstance.h"
#include "Surelog/Design/Netlist.h"
#include "Surelog/Design/ParamAssign.h"
#include "Surelog/Design/Parameter.h"
#include "Surelog/Design/Signal.h"
#include "Surelog/Design/SimpleType.h"
#include "Surelog/Design/Statement.h"
#include "Surelog/Design/Struct.h"
#include "Surelog/Design/TfPortItem.h"
#include "Surelog/Design/Union.h"
#include "Surelog/Design/VObject.h"
#include "Surelog/Design/ValuedComponentI.h"
#include "Surelog/DesignCompile/CompileDesign.h"
#include "Surelog/DesignCompile/UhdmWriter.h"
#include "Surelog/ErrorReporting/Error.h"
#include "Surelog/ErrorReporting/ErrorContainer.h"
#include "Surelog/ErrorReporting/ErrorDefinition.h"
#include "Surelog/ErrorReporting/Location.h"
#include "Surelog/Library/Library.h"
#include "Surelog/Package/Package.h"
#include "Surelog/SourceCompile/Compiler.h"
#include "Surelog/SourceCompile/SymbolTable.h"
#include "Surelog/SourceCompile/VObjectTypes.h"
#include "Surelog/Testbench/ClassDefinition.h"
#include "Surelog/Testbench/Program.h"
#include "Surelog/Testbench/TypeDef.h"
#include "Surelog/Testbench/Variable.h"
#include "Surelog/Utils/NumUtils.h"
#include "Surelog/Utils/StringUtils.h"

// UHDM
#include <uhdm/BaseClass.h>
#include <uhdm/ElaboratorListener.h>
#include <uhdm/ExprEval.h>
#include <uhdm/clone_tree.h>
#include <uhdm/expr.h>
#include <uhdm/sv_vpi_user.h>
#include <uhdm/uhdm.h>
#include <uhdm/uhdm_types.h>
#include <uhdm/vpi_user.h>

#include <algorithm>
#include <climits>
#include <cstdint>
#include <cstdlib>
#include <cstring>
#include <functional>
#include <map>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

namespace SURELOG {

using namespace UHDM;  // NOLINT (we use a good chunk of these here)

void CompileHelper::checkForLoops(bool on) {
  m_checkForLoops = on;
  m_stackLevel = 0;
  m_unwind = false;
}

bool CompileHelper::loopDetected(PathId fileId, uint32_t lineNumber,
                                 CompileDesign* compileDesign,
                                 ValuedComponentI* instance) {
#if defined(_WIN32) || defined(__MINGW32__) || defined(__CYGWIN__)
  constexpr int32_t kMaxAllowedStackDepth = 100;
#else
  constexpr int32_t kMaxAllowedStackDepth = 1000;
#endif
  if (m_checkForLoops) {
    if ((m_stackLevel > kMaxAllowedStackDepth) || (m_unwind)) {
      std::string instName;
      if (ModuleInstance* inst =
              valuedcomponenti_cast<ModuleInstance*>(instance)) {
        instName = inst->getFullPathName();
      }
      Location loc(fileId, lineNumber, 0, m_symbols->registerSymbol(instName));
      Error err(ErrorDefinition::ELAB_EXPRESSION_LOOP, loc);
      m_errors->addError(err);
      m_unwind = true;
      return true;
    }
  }
  return false;
}

bool CompileHelper::importPackage(DesignComponent* scope, Design* design,
                                  const FileContent* fC, NodeId id,
                                  CompileDesign* compileDesign,
                                  bool inPackage) {
  Serializer& s = compileDesign->getSerializer();
  FileCNodeId fnid(fC, id);
  scope->addObject(VObjectType::paPackage_import_item, fnid);

  NodeId nameId = fC->Child(id);
  const std::string_view pack_name = fC->SymName(nameId);
  std::string object_name;
  if (NodeId objId = fC->Sibling(nameId)) {
    if (fC->Type(objId) == VObjectType::slStringConst) {
      object_name = fC->SymName(objId);
    }
  }
  Package* def = design->getPackage(pack_name);
  if (def) {
    if (def == scope)  // skip
      return true;
    scope->addAccessPackage(def);
    auto& classSet = def->getObjects(VObjectType::paClass_declaration);
    for (const auto& cls : classSet) {
      const FileContent* packageFile = cls.fC;
      NodeId classDef = packageFile->Sibling(cls.nodeId);
      const std::string_view name = packageFile->SymName(classDef);
      if (!object_name.empty()) {
        if (name != object_name) continue;
      }
      std::string fullName = StrCat(def->getName(), "::", name);
      DesignComponent* comp = packageFile->getComponentDefinition(fullName);
      FileCNodeId fnid(packageFile, classDef);
      scope->addNamedObject(name, fnid, comp);
      scope->insertDataType(name, (ClassDefinition*)comp);
    }
    // Typespecs
    auto& typeSet = def->getDataTypeMap();
    for (auto& type : typeSet) {
      if (!object_name.empty()) {
        if (type.first != object_name) continue;
      }
      scope->insertDataType(type.first, type.second);
    }
    // Variables
    auto& variableSet = def->getVariables();
    for (auto& var : variableSet) {
      if (!object_name.empty()) {
        if (var.first != object_name) continue;
      }
      scope->addVariable(var.second);
      Value* val = def->getValue(var.first);
      if (val) {
        scope->setValue(var.first, m_exprBuilder.clone(val), m_exprBuilder);
      }
    }
    // Nets
    auto& netSet = def->getSignals();
    for (auto& net : netSet) {
      if (!object_name.empty()) {
        if (net->getName() != object_name) continue;
      }
      scope->getSignals().push_back(net);
    }
    // Incomplete bindings
    for (auto& var : def->getLateBinding()) {
      scope->needLateBinding(var);
    }
    for (auto& var : def->getLateTypedefBinding()) {
      scope->needLateTypedefBinding(var);
    }

    // Type parameters
    auto& paramSet = def->getParameterMap();
    for (auto& param : paramSet) {
      if (!object_name.empty()) {
        if (param.first != object_name) continue;
      }
      Parameter* orig = param.second;
      Parameter* clone = new Parameter(*orig);
      clone->setImportedPackage(pack_name);
      scope->insertParameter(clone);
      UHDM::any* p = orig->getUhdmParam();

      UHDM::VectorOfany* parameters = scope->getParameters();
      if (parameters == nullptr) {
        scope->setParameters(s.MakeAnyVec());
        parameters = scope->getParameters();
      }

      if (p) {
        ElaboratorContext elaboratorContext(&s, false, true);
        any* pclone = UHDM::clone_tree(p, &elaboratorContext);
        if (pclone->UhdmType() == uhdmtype_parameter) {
          type_parameter* the_p = (type_parameter*)pclone;
          the_p->VpiImported(pack_name);
          if (const ref_typespec* rt = the_p->Typespec()) {
            if (rt->Actual_typespec<unsupported_typespec>() != nullptr) {
              scope->needLateTypedefBinding(the_p);
            }
          }
        } else {
          parameter* the_p = (parameter*)pclone;
          the_p->VpiImported(pack_name);
          if (const ref_typespec* rt = the_p->Typespec()) {
            if (rt->Actual_typespec<unsupported_typespec>() != nullptr) {
              scope->needLateTypedefBinding(the_p);
            }
          }
        }
        parameters->push_back(pclone);
        clone->setUhdmParam(pclone);
      }
    }

    // Regular parameter
    auto& params = def->getParamAssignVec();
    for (ParamAssign* orig : params) {
      if (!object_name.empty()) {
        UHDM::param_assign* pass = orig->getUhdmParamAssign();
        if (pass->Lhs()->VpiName() != object_name) continue;
      }
      ParamAssign* clone = new ParamAssign(*orig);
      scope->addParamAssign(clone);
      UHDM::param_assign* pass = clone->getUhdmParamAssign();

      UHDM::VectorOfparam_assign* param_assigns = scope->getParam_assigns();
      if (param_assigns == nullptr) {
        scope->setParam_assigns(s.MakeParam_assignVec());
        param_assigns = scope->getParam_assigns();
      }
      UHDM::VectorOfany* parameters = scope->getParameters();
      if (parameters == nullptr) {
        scope->setParameters(s.MakeAnyVec());
        parameters = scope->getParameters();  // NOLINT(*.DeadStores)
      }

      ElaboratorContext elaboratorContext(&s, false, true);
      UHDM::param_assign* cpass =
          (UHDM::param_assign*)UHDM::clone_tree(pass, &elaboratorContext);
      clone->setUhdmParamAssign(cpass);
      param_assigns->push_back(cpass);
      UHDM::any* orig_p = (UHDM::any*)cpass->Lhs();
      UHDM::any* pclone =
          orig_p;  // The param_assign clone already cloned the param
      cpass->Lhs(pclone);
      if (pclone->UhdmType() == uhdmparameter) {
        parameter* the_p = (parameter*)pclone;
        the_p->VpiImported(pack_name);
        if (const ref_typespec* rt = the_p->Typespec()) {
          if (rt->Actual_typespec<unsupported_typespec>() != nullptr) {
            scope->needLateTypedefBinding(the_p);
          }
        }
      }
    }

    // Values (from enum declarations...)
    auto& values = def->getMappedValues();
    for (auto& mvalue : values) {
      if (!object_name.empty()) {
        if (mvalue.first != object_name) continue;
      }
      if (mvalue.second.first->isValid())
        scope->setValue(mvalue.first, m_exprBuilder.clone(mvalue.second.first),
                        m_exprBuilder, mvalue.second.second);
    }
    for (auto& cvalue : def->getComplexValues()) {
      if (!object_name.empty()) {
        if (cvalue.first != object_name) continue;
      }
      scope->setComplexValue(cvalue.first, cvalue.second);
    }

    // tasks/functions
    VectorOftask_func* funcs = def->getTask_funcs();
    if (funcs) {
      VectorOftask_func* sfuncs = scope->getTask_funcs();
      if (sfuncs == nullptr) {
        sfuncs = s.MakeTask_funcVec();
      }
      for (auto& func : *funcs) {
        if (!object_name.empty()) {
          if (func->VpiName() != object_name) continue;
        }
        bool duplicate = false;
        for (auto& f : *sfuncs) {
          if (f->VpiName() == func->VpiName()) {
            duplicate = true;
            break;
          }
        }
        if (!duplicate) {
          if (inPackage) {
            ElaboratorContext elaboratorContext(&s, false,
                                                /*mute errors */ true);
            task_func* clone =
                (task_func*)UHDM::clone_tree((any*)func, &elaboratorContext);
            sfuncs->push_back(clone);
          } else {
            sfuncs->push_back(func);
          }
        }
      }
      scope->setTask_funcs(sfuncs);
    }
  } else {
    Location loc(fC->getFileId(id), fC->Line(id), fC->Column(id),
                 m_symbols->registerSymbol(pack_name));
    Error err(ErrorDefinition::COMP_UNDEFINED_PACKAGE, loc);
    m_errors->addError(err);
  }

  return true;
}

UHDM::constant* CompileHelper::constantFromValue(Value* val,
                                                 CompileDesign* compileDesign) {
  Serializer& s = compileDesign->getSerializer();
  Value::Type valueType = val->getType();
  UHDM::constant* c = nullptr;
  switch (valueType) {
    case Value::Type::Scalar: {
      c = s.MakeConstant();
      c->VpiConstType(vpiScalarVal);
      c->VpiValue(val->uhdmValue());
      c->VpiDecompile(val->decompiledValue());
      c->VpiSize(1);
      break;
    }
    case Value::Type::Binary: {
      c = s.MakeConstant();
      c->VpiConstType(vpiBinStrVal);
      c->VpiValue(val->uhdmValue());
      c->VpiDecompile(val->decompiledValue());
      c->VpiSize(val->getSize());
      break;
    }
    case Value::Type::Hexadecimal: {
      c = s.MakeConstant();
      c->VpiConstType(vpiHexStrVal);
      c->VpiValue(val->uhdmValue());
      c->VpiDecompile(val->decompiledValue());
      c->VpiSize(val->getSize());
      break;
    }
    case Value::Type::Octal: {
      c = s.MakeConstant();
      c->VpiConstType(vpiOctStrVal);
      c->VpiValue(val->uhdmValue());
      c->VpiDecompile(val->decompiledValue());
      c->VpiSize(val->getSize());
      break;
    }
    case Value::Type::Unsigned:
    case Value::Type::Integer: {
      c = s.MakeConstant();
      c->VpiConstType(vpiIntVal);
      c->VpiValue(val->uhdmValue());
      c->VpiDecompile(val->decompiledValue());
      c->VpiSize(val->getSize());
      break;
    }
    case Value::Type::Double: {
      c = s.MakeConstant();
      c->VpiConstType(vpiRealVal);
      c->VpiValue(val->uhdmValue());
      c->VpiDecompile(val->decompiledValue());
      c->VpiSize(val->getSize());
      break;
    }
    case Value::Type::String: {
      c = s.MakeConstant();
      c->VpiConstType(vpiStringVal);
      c->VpiValue(val->uhdmValue());
      c->VpiDecompile(val->decompiledValue());
      c->VpiSize(val->getSize());
      break;
    }
    case Value::Type::None:
    default: {
      // return nullptr
    }
  }
  return c;
}

bool CompileHelper::compileTfPortList(Procedure* parent, const FileContent* fC,
                                      NodeId tf_port_list,
                                      TfPortList& targetList) {
  bool result = true;
  /*
   n<c1> u<7> t<StringConst> p<29> s<27> l<10>
   n<> u<8> t<IntegerAtomType_Int> p<9> l<12>
   n<> u<9> t<Data_type> p<10> c<8> l<12>
   n<> u<10> t<Function_data_type> p<11> c<9> l<12>
   n<> u<11> t<Function_data_type_or_implicit> p<24> c<10> s<12> l<12>
   n<try_get> u<12> t<StringConst> p<24> s<22> l<12>
   n<> u<13> t<IntegerAtomType_Int> p<14> l<12>
   n<> u<14> t<Data_type> p<15> c<13> l<12>
   n<> u<15> t<Data_type_or_implicit> p<21> c<14> s<16> l<12>
   n<keyCount> u<16> t<StringConst> p<21> s<20> l<12>
   n<1> u<17> t<IntConst> p<18> l<12>
   n<> u<18> t<Primary_literal> p<19> c<17> l<12>
   n<> u<19> t<Primary> p<20> c<18> l<12>
   n<> u<20> t<Expression> p<21> c<19> l<12>
   n<> u<21> t<Tf_port_item> p<22> c<15> l<12>
   n<> u<22> t<Tf_port_list> p<24> c<21> s<23> l<12>
   n<> u<23> t<Endfunction> p<24> l<13>
   n<> u<24> t<Function_body_declaration> p<25> c<11> l<12>
   n<> u<25> t<Function_declaration> p<26> c<24> l<12>
   n<> u<26> t<Class_method> p<27> c<25> l<12>
  */
  /*
   Or
   n<get> u<47> t<StringConst> p<55> s<53> l<18>
   n<> u<48> t<PortDir_Ref> p<49> l<18>
   n<> u<49> t<Tf_port_direction> p<52> c<48> s<50> l<18>
   n<> u<50> t<Data_type_or_implicit> p<52> s<51> l<18>
   n<message> u<51> t<StringConst> p<52> l<18>
   n<> u<52> t<Tf_port_item> p<53> c<49> l<18>
  */
  // Compile arguments
  if (tf_port_list && (fC->Type(tf_port_list) == VObjectType::paTf_port_list)) {
    NodeId tf_port_item = fC->Child(tf_port_list);
    while (tf_port_item) {
      Value* value = nullptr;
      NodeId tf_data_type_or_implicit = fC->Child(tf_port_item);
      NodeId tf_data_type = fC->Child(tf_data_type_or_implicit);
      VObjectType tf_port_direction_type = fC->Type(tf_data_type_or_implicit);
      NodeId tf_param_name = fC->Sibling(tf_data_type_or_implicit);
      if (tf_port_direction_type == VObjectType::paTfPortDir_Ref ||
          tf_port_direction_type == VObjectType::paTfPortDir_ConstRef ||
          tf_port_direction_type == VObjectType::paTfPortDir_Inp ||
          tf_port_direction_type == VObjectType::paTfPortDir_Out ||
          tf_port_direction_type == VObjectType::paTfPortDir_Inout) {
        tf_data_type = fC->Sibling(tf_data_type_or_implicit);
        tf_param_name = fC->Sibling(tf_data_type);
      } else {
        tf_port_direction_type = VObjectType::sl_INVALID_;
      }
      NodeId type = fC->Child(tf_data_type);
      VObjectType the_type = fC->Type(type);
      std::string typeName;
      if (the_type == VObjectType::slStringConst) {
        typeName = fC->SymName(type);
      } else if (the_type == VObjectType::paClass_scope) {
        NodeId class_type = fC->Child(type);
        NodeId class_name = fC->Child(class_type);
        NodeId symb_id = fC->Sibling(type);
        typeName.assign(fC->SymName(class_name))
            .append("::")
            .append(fC->SymName(symb_id));
      } else {
        typeName = VObject::getTypeName(the_type);
      }
      const std::string_view name = fC->SymName(tf_param_name);
      NodeId expression = fC->Sibling(tf_param_name);
      DataType* dtype = new DataType(fC, type, typeName, fC->Type(type));

      if (expression &&
          (fC->Type(expression) != VObjectType::paVariable_dimension) &&
          (dtype->getType() != VObjectType::slStringConst)) {
        value = m_exprBuilder.evalExpr(fC, expression, parent->getParent());
      }
      NodeId range;
      TfPortItem* param = new TfPortItem(parent, fC, tf_port_item, range, name,
                                         dtype, value, tf_port_direction_type);
      targetList.push_back(param);
      tf_port_item = fC->Sibling(tf_port_item);
    }
  }
  return result;
}

const DataType* CompileHelper::compileTypeDef(DesignComponent* scope,
                                              const FileContent* fC,
                                              NodeId data_declaration,
                                              CompileDesign* compileDesign,
                                              Reduce reduce, UHDM::any* pstmt) {
  DataType* newType = nullptr;
  Serializer& s = compileDesign->getSerializer();
  UHDM::VectorOftypespec* typespecs = nullptr;
  if (pstmt) {
    UHDM::scope* scope = any_cast<UHDM::scope*>(pstmt);
    if (scope) {
      typespecs = scope->Typespecs();
      if (typespecs == nullptr) {
        typespecs = s.MakeTypespecVec();
        scope->Typespecs(typespecs);
      }
    }
  }
  /*
   n<> u<1> t<IntVec_TypeBit> p<12> s<11> l<5>
   n<1> u<2> t<IntConst> p<3> l<5>
   n<> u<3> t<Primary_literal> p<4> c<2> l<5>
   n<> u<4> t<Constant_primary> p<5> c<3> l<5>
   n<> u<5> t<Constant_expression> p<10> c<4> s<9> l<5>
   n<0> u<6> t<IntConst> p<7> l<5>
   n<> u<7> t<Primary_literal> p<8> c<6> l<5>
   n<> u<8> t<Constant_primary> p<9> c<7> l<5>
   n<> u<9> t<Constant_expression> p<10> c<8> l<5>
   n<> u<10> t<Constant_range> p<11> c<5> l<5>
   n<> u<11> t<Packed_dimension> p<12> c<10> l<5>
   n<> u<12> t<Enum_base_type> p<21> c<1> s<14> l<5>
   n<UVM_INFO> u<13> t<StringConst> p<14> l<7>
   n<> u<14> t<Enum_name_declaration> p<21> c<13> s<16> l<7>
   n<UVM_WARNING> u<15> t<StringConst> p<16> l<8>
   n<> u<16> t<Enum_name_declaration> p<21> c<15> s<18> l<8>
   n<UVM_ERROR> u<17> t<StringConst> p<18> l<9>
   n<> u<18> t<Enum_name_declaration> p<21> c<17> s<20> l<9>
   n<UVM_FATAL> u<19> t<StringConst> p<20> l<10>
   n<> u<20> t<Enum_name_declaration> p<21> c<19> l<10>
   n<> u<21> t<Data_type> p<23> c<12> s<22> l<5>
   n<uvm_severity> u<22> t<StringConst> p<23> l<11>
   n<> u<23> t<Type_declaration> p<24> c<21> l<5>
   n<> u<24> t<Data_declaration> p<25> c<23> l<5>
   */

  NodeId type_declaration = fC->Child(data_declaration);
  NodeId data_type = fC->Child(type_declaration);

  VObjectType dtype = fC->Type(data_type);
  NodeId type_name;
  if (dtype == VObjectType::paClass_keyword ||
      dtype == VObjectType::paStruct_keyword ||
      dtype == VObjectType::paUnion_keyword ||
      dtype == VObjectType::paInterface_class_keyword ||
      dtype == VObjectType::paEnum_keyword) {
    type_name = fC->Sibling(data_type);
    const std::string_view name = fC->SymName(type_name);
    const TypeDef* prevDef = scope->getTypeDef(name);
    if (prevDef) return prevDef;
    if (fC->Type(type_name) == VObjectType::slStringConst) {
      TypeDef* newTypeDef = new TypeDef(fC, type_declaration, type_name, name);
      scope->insertTypeDef(newTypeDef);
      newType = newTypeDef;
      return newType;
    }
  } else if (dtype == VObjectType::slStringConst) {
    NodeId btype = data_type;
    NodeId Select = fC->Sibling(btype);
    if (fC->Type(Select) == VObjectType::paConstant_bit_select) {
      NodeId subType = fC->Sibling(Select);
      NodeId nameId = fC->Sibling(subType);
      if (nameId) {
        data_type = subType;
      } else {
        return nullptr;
      }
      type_name = fC->Sibling(data_type);
      data_type = btype;
    }
  } else {
    if (dtype != VObjectType::paData_type) {
      return nullptr;
    }
    type_name = fC->Sibling(data_type);
  }

  const NodeId Variable_dimension = fC->Sibling(type_name);
  array_typespec* array_tps = nullptr;
  packed_array_typespec* packed_array_tps = nullptr;
  function* resolution_func = nullptr;
  std::string resolutionFunctionName;
  if (Variable_dimension) {
    if (fC->Type(Variable_dimension) == VObjectType::slStringConst) {
      std::string_view name = fC->SymName(Variable_dimension);
      std::pair<task_func*, DesignComponent*> ret =
          getTaskFunc(name, scope, compileDesign, nullptr, nullptr);
      task_func* tf = ret.first;
      resolution_func = any_cast<function*>(tf);
      resolutionFunctionName = name;
    } else {
      array_tps = s.MakeArray_typespec();
      fC->populateCoreMembers(
          data_type, Variable_dimension ? Variable_dimension : data_type,
          array_tps);
      int32_t size;
      if (VectorOfrange* ranges =
              compileRanges(scope, fC, Variable_dimension, compileDesign,
                            reduce, array_tps, nullptr, size, false)) {
        array_tps->Ranges(ranges);
      }
    }
  }
  std::string_view name = fC->SymName(type_name);
  std::string fullName(name);
  if (Package* pack = valuedcomponenti_cast<Package*>(scope)) {
    fullName.assign(pack->getName()).append("::").append(name);
  }
  if (scope) {
    const TypeDef* prevDef = scope->getTypeDef(name);
    if (prevDef && !prevDef->isForwardDeclaration()) {
      Location loc1(fC->getFileId(data_type), fC->Line(data_type),
                    fC->Column(data_type), m_symbols->registerSymbol(name));
      const FileContent* prevFile = prevDef->getFileContent();
      NodeId prevNode = prevDef->getNodeId();
      Location loc2(prevFile->getFileId(prevNode), prevFile->Line(prevNode),
                    prevFile->Column(prevNode),
                    m_symbols->registerSymbol(name));
      Error err(ErrorDefinition::COMP_MULTIPLY_DEFINED_TYPEDEF, loc1, loc2);
      m_errors->addError(err);
    }
  }

  VObjectType base_type = fC->Type(data_type);

  DataType* type = new DataType(fC, data_type, name, base_type);
  if (scope) scope->insertDataType(name, type);

  // Enum or Struct or Union
  NodeId enum_base_type = fC->Child(data_type);
  bool enumType = false;
  bool structType = false;
  NodeId Packed_dimension = fC->Sibling(enum_base_type);
  if (Packed_dimension &&
      (fC->Type(Packed_dimension) == VObjectType::paPacked_dimension)) {
    packed_array_tps = s.MakePacked_array_typespec();
    fC->populateCoreMembers(data_type, data_type, packed_array_tps);
    int32_t size;
    if (VectorOfrange* ranges =
            compileRanges(scope, fC, Packed_dimension, compileDesign, reduce,
                          packed_array_tps, nullptr, size, false)) {
      packed_array_tps->Ranges(ranges);
    }
  }
  NodeId enum_name_declaration;
  if (fC->Type(enum_base_type) == VObjectType::paEnum_base_type) {
    enum_name_declaration = fC->Sibling(enum_base_type);
    enumType = true;
  } else if (fC->Type(enum_base_type) == VObjectType::paEnum_name_declaration) {
    enumType = true;
    enum_name_declaration = enum_base_type;
    enum_base_type = InvalidNodeId;
  } else if (fC->Type(enum_base_type) == VObjectType::paStruct_union) {
    structType = true;
    NodeId struct_or_union = fC->Child(enum_base_type);
    VObjectType struct_or_union_type = fC->Type(struct_or_union);
    TypeDef* newTypeDef = new TypeDef(fC, type_declaration, type_name, name);

    if (struct_or_union_type == VObjectType::paStruct_keyword) {
      Struct* st = new Struct(fC, type_name, enum_base_type);
      newTypeDef->setDataType(st);
      newTypeDef->setDefinition(st);
      UHDM::typespec* ts =
          compileTypespec(scope, fC, enum_base_type, compileDesign, reduce,
                          nullptr, nullptr, false);
      fC->populateCoreMembers(data_type, data_type, ts);
      if ((reduce == Reduce::Yes) && (valuedcomponenti_cast<Package*>(scope))) {
        ts->Instance(scope->getUhdmInstance());
      }
      if (array_tps) {
        st->setTypespec(array_tps);
        if (array_tps->Elem_typespec() == nullptr) {
          ref_typespec* rt = s.MakeRef_typespec();
          rt->VpiParent(array_tps);
          array_tps->Elem_typespec(rt);
        }
        array_tps->Elem_typespec()->Actual_typespec(ts);
        array_tps->VpiName(fullName);
        if (typespecs) typespecs->push_back(array_tps);
      } else if (packed_array_tps) {
        st->setTypespec(packed_array_tps);
        if (packed_array_tps->Elem_typespec() == nullptr) {
          ref_typespec* rt = s.MakeRef_typespec();
          rt->VpiParent(packed_array_tps);
          packed_array_tps->Elem_typespec(rt);
        }
        packed_array_tps->Elem_typespec()->Actual_typespec(ts);
        packed_array_tps->VpiName(fullName);
        if (typespecs) typespecs->push_back(packed_array_tps);
      } else {
        ts->VpiName(fullName);
        st->setTypespec(ts);
        if (typespecs) typespecs->push_back(ts);
      }
    } else if (struct_or_union_type == VObjectType::paUnion_keyword) {
      Union* st = new Union(fC, type_name, enum_base_type);
      newTypeDef->setDataType(st);
      newTypeDef->setDefinition(st);
      UHDM::typespec* ts =
          compileTypespec(scope, fC, enum_base_type, compileDesign, reduce,
                          nullptr, nullptr, false);
      fC->populateCoreMembers(data_type, data_type, ts);
      if ((reduce == Reduce::Yes) && (valuedcomponenti_cast<Package*>(scope))) {
        ts->Instance(scope->getUhdmInstance());
      }
      if (array_tps) {
        st->setTypespec(array_tps);
        if (array_tps->Elem_typespec() == nullptr) {
          ref_typespec* rt = s.MakeRef_typespec();
          rt->VpiParent(array_tps);
          array_tps->Elem_typespec(rt);
        }
        array_tps->Elem_typespec()->Actual_typespec(ts);
        array_tps->VpiName(fullName);
        if (typespecs) typespecs->push_back(array_tps);
      } else if (packed_array_tps) {
        st->setTypespec(packed_array_tps);
        if (packed_array_tps->Elem_typespec() == nullptr) {
          ref_typespec* rt = s.MakeRef_typespec();
          rt->VpiParent(packed_array_tps);
          packed_array_tps->Elem_typespec(rt);
        }
        packed_array_tps->Elem_typespec()->Actual_typespec(ts);
        packed_array_tps->VpiName(fullName);
        if (typespecs) typespecs->push_back(packed_array_tps);
      } else {
        ts->VpiName(fullName);
        st->setTypespec(ts);
        if (typespecs) typespecs->push_back(ts);
      }
    }

    if (scope) {
      DesignComponent::DataTypeMap dmap = scope->getDataTypeMap();
      DesignComponent::DataTypeMap::iterator itr = dmap.find(name);
      if (itr != dmap.end()) {
        dmap.erase(itr);
      }
    }

    type->setDefinition(newTypeDef);
    if (scope) scope->insertTypeDef(newTypeDef);
    newType = newTypeDef;
  }
  if (enumType) {
    TypeDef* newTypeDef =
        new TypeDef(fC, type_declaration, enum_base_type, name);
    int32_t val = 0;
    Enum* the_enum = new Enum(fC, type_name, enum_base_type);
    newTypeDef->setDataType(the_enum);
    newTypeDef->setDefinition(the_enum);
    the_enum->setBaseTypespec(
        compileTypespec(scope, fC, fC->Child(enum_base_type), compileDesign,
                        reduce, nullptr, nullptr, false));

    UHDM::enum_typespec* enum_t = s.MakeEnum_typespec();

    if (array_tps) {
      the_enum->setTypespec(array_tps);
      if (array_tps->Elem_typespec() == nullptr) {
        ref_typespec* rt = s.MakeRef_typespec();
        rt->VpiParent(array_tps);
        array_tps->Elem_typespec(rt);
      }
      array_tps->Elem_typespec()->Actual_typespec(enum_t);
      array_tps->VpiName(name);
      if (typespecs) typespecs->push_back(array_tps);
    } else if (packed_array_tps) {
      the_enum->setTypespec(packed_array_tps);
      if (packed_array_tps->Elem_typespec() == nullptr) {
        ref_typespec* rt = s.MakeRef_typespec();
        rt->VpiParent(packed_array_tps);
        packed_array_tps->Elem_typespec(rt);
      }
      packed_array_tps->Elem_typespec()->Actual_typespec(enum_t);
      packed_array_tps->VpiName(name);
      if (typespecs) typespecs->push_back(packed_array_tps);
    } else {
      enum_t->VpiName(fullName);
      the_enum->setTypespec(enum_t);
      if (typespecs) typespecs->push_back(enum_t);
    }

    the_enum->getFileContent()->populateCoreMembers(type_declaration,
                                                    type_declaration, enum_t);

    // Enum basetype
    if (UHDM::typespec* basets = the_enum->getBaseTypespec()) {
      if (enum_t->Base_typespec() == nullptr) {
        ref_typespec* rt = s.MakeRef_typespec();
        rt->VpiParent(enum_t);
        enum_t->Base_typespec(rt);
      }
      enum_t->Base_typespec()->Actual_typespec(basets);
    }
    if ((reduce == Reduce::Yes) && (valuedcomponenti_cast<Package*>(scope))) {
      enum_t->Instance(scope->getUhdmInstance());
    }
    // Enum values
    VectorOfenum_const* econsts = s.MakeEnum_constVec();
    enum_t->Enum_consts(econsts);
    uint64_t baseSize = 64;
    if (const ref_typespec* rt = enum_t->Base_typespec()) {
      if (const typespec* ts = rt->Actual_typespec()) {
        bool invalidValue = false;
        baseSize = Bits(ts, invalidValue, scope, compileDesign, reduce, nullptr,
                        fC->getFileId(), ts->VpiLineNo(), true);
      }
    }
    while (enum_name_declaration) {
      NodeId enumNameId = fC->Child(enum_name_declaration);
      const std::string_view enumName = fC->SymName(enumNameId);
      NodeId enumValueId = fC->Sibling(enumNameId);
      Value* value = nullptr;
      if (enumValueId) {
        any* exp = compileExpression(scope, fC, enumValueId, compileDesign,
                                     reduce, pstmt, nullptr);
        if (exp && (exp->UhdmType() == uhdmconstant)) {
          constant* c = (constant*)exp;
          value = m_exprBuilder.fromVpiValue(c->VpiValue(), c->VpiSize());
          bool invalidValue = false;
          int32_t ct = c->VpiConstType();
          if (ct == vpiIntConst || ct == vpiUIntConst || ct == vpiDecConst ||
              ct == vpiBinaryConst || ct == vpiHexConst || ct == vpiOctConst) {
            UHDM::ExprEval eval;
            int64_t v = eval.get_value(invalidValue, c);
            if (!invalidValue) val = v;
          }
        } else {
          value = m_exprBuilder.evalExpr(fC, enumValueId, scope);
          value->setValid();
        }
      }
      if (value == nullptr) {
        value = m_exprBuilder.getValueFactory().newLValue();
        value->set(val, Value::Type::Integer, baseSize);
      }
      the_enum->addValue(enumName, fC->Line(enumNameId), value);
      val++;
      if (scope) scope->setValue(enumName, value, m_exprBuilder);
      Variable* variable =
          new Variable(type, fC, enumValueId, InvalidNodeId, enumName);
      if (scope) scope->addVariable(variable);

      enum_const* econst = s.MakeEnum_const();
      econst->VpiName(enumName);
      econst->VpiParent(enum_t);
      fC->populateCoreMembers(enum_name_declaration, enum_name_declaration,
                              econst);
      econst->VpiValue(value->uhdmValue());
      if (enumValueId) {
        if (any* exp = compileExpression(scope, fC, enumValueId, compileDesign,
                                         reduce, econst, nullptr)) {
          UHDM::ExprEval eval;
          econst->VpiDecompile(eval.prettyPrint(exp));
        }
      } else {
        econst->VpiDecompile(value->decompiledValue());
      }
      econst->VpiSize(value->getSize());
      econsts->push_back(econst);
      enum_name_declaration = fC->Sibling(enum_name_declaration);
    }

    type->setDefinition(newTypeDef);
    if (scope) scope->insertTypeDef(newTypeDef);
    newType = newTypeDef;

  } else if (structType) {
  } else {
    bool forwardDeclaration = false;
    NodeId stype = fC->Child(data_type);
    if (fC->Type(stype) == VObjectType::paVIRTUAL) stype = fC->Sibling(stype);
    if (!stype && (fC->Type(data_type) == VObjectType::slStringConst)) {
      stype = data_type;
      if (!fC->Sibling(stype)) {
        name = fC->SymName(stype);
        forwardDeclaration = true;
      }
    }
    if ((fC->Type(stype) == VObjectType::slStringConst) ||
        fC->Type(stype) == VObjectType::paClass_scope) {
      TypeDef* newTypeDef =
          new TypeDef(fC, type_declaration, stype, name, forwardDeclaration);
      type->setDefinition(newTypeDef);
      if (scope) scope->insertTypeDef(newTypeDef);
      DummyType* dummy = new DummyType(fC, type_name, stype);
      newTypeDef->setDataType(dummy);
      newTypeDef->setDefinition(dummy);
      // Don't create the typespec here, as it is most likely going to be
      // incomplete at compilation time, except for packages and FileContent
      if ((reduce == Reduce::Yes) &&
          ((valuedcomponenti_cast<Package*>(scope) ||
            valuedcomponenti_cast<FileContent*>(scope)))) {
        UHDM::typespec* ts = compileTypespec(scope, fC, stype, compileDesign,
                                             reduce, nullptr, nullptr, false);
        if (ts && (ts->UhdmType() != uhdmclass_typespec) &&
            (ts->UhdmType() != uhdmunsupported_typespec)) {
          ElaboratorContext elaboratorContext(&s, false, true);
          typespec* tpclone =
              (typespec*)UHDM::clone_tree((any*)ts, &elaboratorContext);

          if (array_tps) {
            array_tps->Instance(scope->getUhdmInstance());
            array_tps->VpiName(name);
            if (array_tps->Elem_typespec() == nullptr) {
              ref_typespec* tpcloneRef = s.MakeRef_typespec();
              tpcloneRef->VpiParent(array_tps);
              array_tps->Elem_typespec(tpcloneRef);
            }
            array_tps->Elem_typespec()->Actual_typespec(tpclone);

            if (tpclone->Typedef_alias() == nullptr) {
              ref_typespec* tsRef = s.MakeRef_typespec();
              tsRef->VpiParent(tpclone);
              tpclone->Typedef_alias(tsRef);
            }
            tpclone->Typedef_alias()->Actual_typespec(ts);
            if (typespecs) typespecs->push_back(array_tps);
            newTypeDef->setTypespec(array_tps);
            dummy->setTypespec(array_tps);
            if (resolution_func) {
              array_tps->Resolution_func(resolution_func);
            } else if (!resolutionFunctionName.empty()) {
              scope->needLateResolutionFunction(resolutionFunctionName,
                                                array_tps);
            }
          } else if (packed_array_tps) {
            if (tpclone->UhdmType() == uhdmlogic_typespec) {
              logic_typespec* logic_array_tps = s.MakeLogic_typespec();
              logic_array_tps->Ranges(packed_array_tps->Ranges());
              logic_array_tps->Instance(scope->getUhdmInstance());
              logic_array_tps->VpiName(name);
              if (logic_array_tps->Elem_typespec() == nullptr) {
                ref_typespec* tpcloneRef = s.MakeRef_typespec();
                tpcloneRef->VpiParent(logic_array_tps);
                logic_array_tps->Elem_typespec(tpcloneRef);
              }
              logic_array_tps->Elem_typespec()->Actual_typespec(tpclone);
              if (resolution_func) {
                logic_array_tps->Resolution_func(resolution_func);
              } else if (!resolutionFunctionName.empty()) {
                scope->needLateResolutionFunction(resolutionFunctionName,
                                                  logic_array_tps);
              }
              if (tpclone->Typedef_alias() == nullptr) {
                ref_typespec* tsRef = s.MakeRef_typespec();
                tsRef->VpiParent(tpclone);
                tpclone->Typedef_alias(tsRef);
              }
              tpclone->Typedef_alias()->Actual_typespec(ts);
              if (typespecs) typespecs->push_back(logic_array_tps);
              newTypeDef->setTypespec(logic_array_tps);
              dummy->setTypespec(logic_array_tps);
            } else {
              if (ts->UhdmType() == uhdmpacked_array_typespec) {
                tpclone->Instance(scope->getUhdmInstance());
                tpclone->VpiName(name);
                if (tpclone->Typedef_alias() == nullptr) {
                  ref_typespec* tsRef = s.MakeRef_typespec();
                  tsRef->VpiParent(tpclone);
                  tpclone->Typedef_alias(tsRef);
                }
                tpclone->Typedef_alias()->Actual_typespec(ts);
                if (resolution_func) {
                  if (tpclone->UhdmType() == uhdmbit_typespec) {
                    bit_typespec* btps = (bit_typespec*)tpclone;
                    btps->Resolution_func(resolution_func);
                  } else if (tpclone->UhdmType() == uhdmlogic_typespec) {
                    logic_typespec* btps = (logic_typespec*)tpclone;
                    btps->Resolution_func(resolution_func);
                  } else if (tpclone->UhdmType() == uhdmstruct_typespec) {
                    struct_typespec* btps = (struct_typespec*)tpclone;
                    btps->Resolution_func(resolution_func);
                  }
                } else if (!resolutionFunctionName.empty()) {
                  scope->needLateResolutionFunction(resolutionFunctionName,
                                                    tpclone);
                }
                if (typespecs) typespecs->push_back(tpclone);
                newTypeDef->setTypespec(tpclone);
                dummy->setTypespec(tpclone);
              } else {
                packed_array_tps->Instance(scope->getUhdmInstance());
                packed_array_tps->VpiName(name);
                if (packed_array_tps->Elem_typespec() == nullptr) {
                  ref_typespec* tpcloneRef = s.MakeRef_typespec();
                  tpcloneRef->VpiParent(packed_array_tps);
                  packed_array_tps->Elem_typespec(tpcloneRef);
                }
                packed_array_tps->Elem_typespec()->Actual_typespec(tpclone);
                if (tpclone->Typedef_alias() == nullptr) {
                  ref_typespec* tsRef = s.MakeRef_typespec();
                  tsRef->VpiParent(tpclone);
                  tpclone->Typedef_alias(tsRef);
                }
                tpclone->Typedef_alias()->Actual_typespec(ts);
                if (resolution_func) {
                  packed_array_tps->Resolution_func(resolution_func);
                } else if (!resolutionFunctionName.empty()) {
                  scope->needLateResolutionFunction(resolutionFunctionName,
                                                    packed_array_tps);
                }
                if (typespecs) typespecs->push_back(packed_array_tps);
                newTypeDef->setTypespec(packed_array_tps);
                dummy->setTypespec(packed_array_tps);
              }
            }
          } else {
            tpclone->Instance(scope->getUhdmInstance());
            tpclone->VpiName(name);
            if (tpclone->Typedef_alias() == nullptr) {
              ref_typespec* tsRef = s.MakeRef_typespec();
              tsRef->VpiParent(tpclone);
              tpclone->Typedef_alias(tsRef);
            }
            tpclone->Typedef_alias()->Actual_typespec(ts);
            if (resolution_func) {
              if (tpclone->UhdmType() == uhdmbit_typespec) {
                bit_typespec* btps = (bit_typespec*)tpclone;
                btps->Resolution_func(resolution_func);
              } else if (tpclone->UhdmType() == uhdmlogic_typespec) {
                logic_typespec* btps = (logic_typespec*)tpclone;
                btps->Resolution_func(resolution_func);
              } else if (tpclone->UhdmType() == uhdmstruct_typespec) {
                struct_typespec* btps = (struct_typespec*)tpclone;
                btps->Resolution_func(resolution_func);
              }
            } else if (!resolutionFunctionName.empty()) {
              scope->needLateResolutionFunction(resolutionFunctionName,
                                                tpclone);
            }
            if (typespecs) typespecs->push_back(tpclone);
            newTypeDef->setTypespec(tpclone);
            dummy->setTypespec(tpclone);
          }
        }
      } else {
        dummy->setUnpackedTypespec(array_tps);
      }

      if (scope) scope->insertTypeDef(newTypeDef);
      newType = newTypeDef;
    } else {
      TypeDef* newTypeDef = new TypeDef(fC, type_declaration, stype, name);
      type->setDefinition(newTypeDef);
      if (scope) scope->insertTypeDef(newTypeDef);
      SimpleType* simple = new SimpleType(fC, type_name, stype);
      newTypeDef->setDataType(simple);
      newTypeDef->setDefinition(simple);
      if (UHDM::typespec* ts =
              compileTypespec(scope, fC, stype, compileDesign, reduce,
                              array_tps, nullptr, false)) {
        if (array_tps) {
          if (array_tps->Elem_typespec() == nullptr) {
            ref_typespec* tsRef = s.MakeRef_typespec();
            tsRef->VpiParent(array_tps);
            array_tps->Elem_typespec(tsRef);
          }
          array_tps->Elem_typespec()->Actual_typespec(ts);
          ts = array_tps;
        }
        if (resolution_func) {
          if (ts->UhdmType() == uhdmbit_typespec) {
            bit_typespec* btps = (bit_typespec*)ts;
            btps->Resolution_func(resolution_func);
          } else if (ts->UhdmType() == uhdmlogic_typespec) {
            logic_typespec* btps = (logic_typespec*)ts;
            btps->Resolution_func(resolution_func);
          } else if (ts->UhdmType() == uhdmstruct_typespec) {
            struct_typespec* btps = (struct_typespec*)ts;
            btps->Resolution_func(resolution_func);
          } else if (ts->UhdmType() == uhdmreal_typespec) {
            real_typespec* btps = (real_typespec*)ts;
            btps->Resolution_func(resolution_func);
          }
        } else if (!resolutionFunctionName.empty()) {
          scope->needLateResolutionFunction(resolutionFunctionName, ts);
        }

        if ((reduce == Reduce::Yes) &&
            (valuedcomponenti_cast<Package*>(scope))) {
          ts->Instance(scope->getUhdmInstance());
        }
        ts->VpiName(name);
        if (typespecs) typespecs->push_back(ts);
        simple->setTypespec(ts);
      }
      newType = newTypeDef;
    }
  }

  return newType;
}

bool CompileHelper::compileScopeBody(Scope* parent, Statement* parentStmt,
                                     const FileContent* fC,
                                     NodeId function_statement_or_null) {
  bool result = true;
  while (function_statement_or_null) {
    VObjectType nodeType = fC->Type(function_statement_or_null);
    switch (nodeType) {
      case VObjectType::paFunction_statement_or_null:
      case VObjectType::paStatement_or_null: {
        NodeId statement = fC->Child(function_statement_or_null);
        NodeId statement_item = fC->Child(statement);
        NodeId item = fC->Child(statement_item);
        VObjectType stmtType = fC->Type(item);
        switch (stmtType) {
          case VObjectType::paSubroutine_call_statement: {
            compileSubroutine_call(parent, parentStmt, fC, item);
            break;
          }
          case VObjectType::paSeq_block:
            compileSeqBlock_stmt(parent, parentStmt, fC, item);
            break;
          case VObjectType::paLoop_statement:
            compileLoop_stmt(parent, parentStmt, fC, item);
            break;
          default:  // stmtType
            break;
        }
        break;
      }
      case VObjectType::paStatement: {
        NodeId statement = function_statement_or_null;
        NodeId statement_item = fC->Child(statement);
        NodeId item = fC->Child(statement_item);
        VObjectType stmtType = fC->Type(item);
        switch (stmtType) {
          case VObjectType::paSubroutine_call_statement: {
            compileSubroutine_call(parent, parentStmt, fC, item);
            break;
          }
          case VObjectType::paSeq_block:
            compileSeqBlock_stmt(parent, parentStmt, fC, item);
            break;
          case VObjectType::paLoop_statement:
            compileLoop_stmt(parent, parentStmt, fC, item);
            break;
          default:  // stmtType
            break;
        }
        break;
      } break;
      case VObjectType::paBlock_item_declaration:
        compileScopeVariable(parent, fC, function_statement_or_null);
        break;
      case VObjectType::paSuper_dot_new: {
        NodeId list_of_arguments = fC->Sibling(function_statement_or_null);
        NodeId expression = fC->Child(list_of_arguments);
        std::vector<SubRoutineArg*> args;
        while (expression) {
          SubRoutineArg* arg = new SubRoutineArg(expression, nullptr);
          args.push_back(arg);
          expression = fC->Sibling(expression);
        }
        std::vector<NodeId> var_chain;
        var_chain.push_back(function_statement_or_null);
        SubRoutineCallStmt* stmt = new SubRoutineCallStmt(
            parent, parentStmt, fC, function_statement_or_null,
            VObjectType::paSubroutine_call_statement, var_chain, "new", args,
            false, false);
        parent->addStmt(stmt);
        if (parentStmt) parentStmt->addStatement(stmt);
        break;
      }
      default:
        break;
    }
    function_statement_or_null = fC->Sibling(function_statement_or_null);
  }

  return result;
}

bool CompileHelper::compileSubroutine_call(Scope* parent, Statement* parentStmt,
                                           const FileContent* fC,
                                           NodeId subroutine_call_statement) {
  /*
  n<d> u<44> t<StringConst> p<48> s<45> l<15>
  n<> u<45> t<Constant_bit_select> p<48> s<46> l<15>
  n<get_current_item> u<46> t<StringConst> p<48> s<47> l<15>
  n<> u<47> t<List_of_arguments> p<48> l<15>
  n<> u<48> t<Subroutine_call> p<49> c<44> l<15>
  n<> u<49> t<Subroutine_call_statement> p<50> c<48> l<15>
  n<> u<50> t<Statement_item> p<51> c<49> l<15>
  n<> u<51> t<Statement> p<52> c<50> l<15>
  n<> u<52> t<Function_statement_or_null> p<61> c<51> s<59> l<15>
  n<foo> u<53> t<StringConst> p<55> s<54> l<16>
  n<> u<54> t<List_of_arguments> p<55> l<16>
  n<> u<55> t<Subroutine_call> p<56> c<53> l<16>
  n<> u<56> t<Subroutine_call_statement> p<57> c<55> l<16>
  n<> u<57> t<Statement_item> p<58> c<56> l<16>
  n<> u<58> t<Statement> p<59> c<57> l<16>
  n<> u<59> t<Function_statement_or_null> p<61> c<58> s<60> l<16>
   */
  std::vector<NodeId> var_chain;
  NodeId subroutine_call = fC->Child(subroutine_call_statement);
  NodeId base_name = fC->Child(subroutine_call);
  NodeId next_name = base_name;
  bool static_call = false;
  bool system_call = false;
  if (fC->Type(base_name) == VObjectType::paDollar_keyword) {
    // system calls
    base_name = fC->Sibling(base_name);
    next_name = base_name;
    system_call = true;
  } else if (fC->Type(base_name) == VObjectType::paImplicit_class_handle) {
    next_name = fC->Sibling(base_name);
    base_name = fC->Child(base_name);
    var_chain.push_back(base_name);
  } else if (fC->Type(base_name) == VObjectType::paClass_scope) {
    next_name = fC->Sibling(base_name);
    base_name = fC->Child(base_name);
    base_name = fC->Child(base_name);
    while (base_name) {
      VObjectType ntype = fC->Type(base_name);
      if (ntype == VObjectType::paParameter_value_assignment) {
        base_name = fC->Sibling(base_name);
      }
      if (!base_name) break;
      var_chain.push_back(base_name);
      base_name = fC->Sibling(base_name);
    }
    static_call = true;
  }
  while (next_name) {
    VObjectType ntype = fC->Type(next_name);
    if (ntype == VObjectType::paConstant_bit_select) {
      next_name = fC->Sibling(next_name);
    }
    if (ntype == VObjectType::paSelect) {
      next_name = fC->Sibling(next_name);
    }
    if (!next_name) break;
    if (ntype == VObjectType::paList_of_arguments) {
      break;
    }
    var_chain.push_back(next_name);

    next_name = fC->Sibling(next_name);
  }
  const std::string_view funcName =
      fC->SymName(var_chain[var_chain.size() - 1]);
  var_chain.pop_back();

  NodeId list_of_arguments = next_name;
  NodeId expression = fC->Child(list_of_arguments);
  std::vector<SubRoutineArg*> args;
  while (expression) {
    SubRoutineArg* arg = new SubRoutineArg(expression, nullptr);
    args.push_back(arg);
    expression = fC->Sibling(expression);
  }

  SubRoutineCallStmt* stmt = new SubRoutineCallStmt(
      parent, parentStmt, fC, subroutine_call,
      VObjectType::paSubroutine_call_statement, var_chain, funcName, args,
      static_call, system_call);
  parent->addStmt(stmt);
  if (parentStmt) parentStmt->addStatement(stmt);
  return true;
}

bool CompileHelper::compileSeqBlock_stmt(Scope* parent, Statement* parentStmt,
                                         const FileContent* fC,
                                         NodeId seq_block) {
  NodeId item = fC->Child(seq_block);
  std::string name;
  SeqBlock* block = new SeqBlock(name, parent, parentStmt, fC, seq_block);
  parent->addScope(block);
  parent->addStmt(block);
  if (parentStmt) parentStmt->addStatement(block);
  compileScopeBody(block, block, fC, item);
  return true;
}

bool CompileHelper::compileLoop_stmt(Scope* parent, Statement* parentStmt,
                                     const FileContent* fC,
                                     NodeId loop_statement) {
  NodeId loop = fC->Child(loop_statement);
  switch (fC->Type(loop)) {
    case VObjectType::paFOR:
      compileForLoop_stmt(parent, parentStmt, fC, fC->Sibling(loop));
      break;
    case VObjectType::paFOREACH:
      compileForeachLoop_stmt(parent, parentStmt, fC, fC->Sibling(loop));
      break;
    default:
      break;
  }
  return true;
}

bool CompileHelper::compileForeachLoop_stmt(
    Scope* parent, Statement* parentStmt, const FileContent* fC,
    NodeId ps_or_hierarchical_array_identifier) {
  NodeId loop_variables = fC->Sibling(ps_or_hierarchical_array_identifier);
  NodeId statement = fC->Sibling(loop_variables);
  ForeachLoopStmt* stmt = new ForeachLoopStmt(
      "", fC->Child(ps_or_hierarchical_array_identifier), parent, parentStmt,
      fC, ps_or_hierarchical_array_identifier,
      VObjectType::paPs_or_hierarchical_array_identifier);
  parent->addStmt(stmt);
  parent->addScope(stmt);
  loop_variables = fC->Child(loop_variables);
  while (loop_variables) {
    stmt->addIteratorId(loop_variables);
    loop_variables = fC->Sibling(loop_variables);
  }
  if (parentStmt) parentStmt->addStatement(stmt);
  compileScopeBody(parent, stmt, fC, statement);

  return true;
}

bool CompileHelper::compileForLoop_stmt(Scope* parent, Statement* parentStmt,
                                        const FileContent* fC,
                                        NodeId first_node) {
  VObjectType init_type = fC->Type(first_node);
  NodeId for_initialization;
  NodeId expression;
  NodeId for_step;
  NodeId statement_or_null;
  NodeId itr_data_type;
  ForLoopStmt* stmt = nullptr;
  if (init_type == VObjectType::paStatement_or_null) {
    // for ( ; ; )
    statement_or_null = first_node;
    stmt = new ForLoopStmt("", parent, parentStmt, fC, first_node,
                           VObjectType::paStatement_or_null);
  } else if (init_type == VObjectType::paFor_initialization) {
    // for ( int32_t i = 0; xxx ; xxx )
    for_initialization = first_node;
    expression = fC->Sibling(for_initialization);
    if (fC->Type(expression) == VObjectType::paExpression)
      for_step = fC->Sibling(expression);
    else {
      for_step = expression;
      expression = InvalidNodeId;
    }
    if (fC->Type(for_step) == VObjectType::paFor_step)
      statement_or_null = fC->Sibling(for_step);
    else {
      statement_or_null = for_step;
      for_step = InvalidNodeId;
    }
    stmt = new ForLoopStmt("", parent, parentStmt, fC, for_initialization,
                           VObjectType::paFor_initialization);
    NodeId for_variable_declaration = fC->Child(for_initialization);
    if (for_variable_declaration)
      itr_data_type = fC->Child(for_variable_declaration);
    NodeId the_data_type = fC->Child(itr_data_type);
    VObjectType the_type = fC->Type(the_data_type);
    stmt->setIteratorType(the_type);
  } else if (init_type == VObjectType::paExpression) {
    // for ( ; i < 1 ; xxx )
    expression = first_node;
    for_step = fC->Sibling(expression);
    if (fC->Type(for_step) == VObjectType::paFor_step)
      statement_or_null = fC->Sibling(for_step);
    else {
      statement_or_null = for_step;
      for_step = InvalidNodeId;
    }
    stmt = new ForLoopStmt("", parent, parentStmt, fC, first_node,
                           VObjectType::paExpression);
  }
  parent->addStmt(stmt);
  parent->addScope(stmt);

  if (expression) stmt->setConditionId(expression);

  if (itr_data_type) {
    NodeId iterator = fC->Sibling(itr_data_type);
    while (iterator) {
      NodeId expression = fC->Sibling(iterator);
      if (expression) {
        stmt->addIteratorId(iterator, expression);
        iterator = fC->Sibling(expression);
      } else {
        stmt->addIteratorId(iterator, InvalidNodeId);
        break;
      }
    }
  }

  if (for_step) {
    NodeId for_step_assignment = fC->Child(for_step);
    while (for_step_assignment) {
      NodeId incr = fC->Child(for_step_assignment);
      stmt->addIteratorStepId(incr);
      for_step_assignment = fC->Sibling(for_step_assignment);
    }
  }

  if (parentStmt) parentStmt->addStatement(stmt);
  compileScopeBody(parent, stmt, fC, statement_or_null);

  return true;
}

bool CompileHelper::compileScopeVariable(Scope* parent, const FileContent* fC,
                                         NodeId id) {
  NodeId data_declaration = fC->Child(id);
  NodeId var_decl = fC->Child(data_declaration);
  VObjectType type = fC->Type(data_declaration);
  if (type == VObjectType::paData_declaration) {
    /*
   n<A> u<3> t<StringConst> p<37> s<12> l<5>
   n<> u<4> t<IntegerAtomType_Int> p<5> l<6>
   n<> u<5> t<Data_type> p<9> c<4> s<8> l<6>
   n<size> u<6> t<StringConst> p<7> l<6>
   n<> u<7> t<Variable_decl_assignment> p<8> c<6> l<6>
   n<> u<8> t<List_of_variable_decl_assignments> p<9> c<7> l<6>
   n<> u<9> t<Variable_declaration> p<10> c<5> l<6>
   n<> u<10> t<Data_declaration> p<11> c<9> l<6>
   n<> u<11> t<Class_property> p<12> c<10> l<6>
   n<> u<12> t<Class_item> p<37> c<11> s<35> l<6>
     */
    VObjectType var_type = fC->Type(var_decl);
    if (var_type == VObjectType::paLifetime_Static) {
      var_decl = fC->Sibling(var_decl);
      var_type = fC->Type(var_decl);
    }
    if (var_type == VObjectType::paVariable_declaration) {
      NodeId data_type = fC->Child(var_decl);
      NodeId node_type = fC->Child(data_type);
      VObjectType the_type = fC->Type(node_type);
      std::string typeName;
      if (the_type == VObjectType::slStringConst) {
        typeName = fC->SymName(node_type);
      } else if (the_type == VObjectType::paClass_scope) {
        NodeId class_type = fC->Child(node_type);
        NodeId class_name = fC->Child(class_type);
        typeName = fC->SymName(class_name);
        typeName += "::";
        NodeId symb_id = fC->Sibling(node_type);
        typeName += fC->SymName(symb_id);
      } else {
        typeName = VObject::getTypeName(the_type);
      }
      DataType* datatype = parent->getUsedDataType(typeName);
      if (!datatype) {
        DataType* type =
            new DataType(fC, node_type, typeName, fC->Type(node_type));
        parent->insertUsedDataType(typeName, type);
        datatype = parent->getUsedDataType(typeName);
      }

      NodeId list_of_variable_decl_assignments = fC->Sibling(data_type);
      NodeId variable_decl_assignment =
          fC->Child(list_of_variable_decl_assignments);
      while (variable_decl_assignment) {
        NodeId var = fC->Child(variable_decl_assignment);
        VObjectType varType = fC->Type(var);
        NodeId range = fC->Sibling(var);
        if (varType == VObjectType::paList_of_arguments) {
          // new ()
        } else {
          const std::string_view varName = fC->SymName(var);

          Variable* previous = parent->getVariable(varName);
          if (previous) {
            Location loc1(fC->getFileId(var), fC->Line(var), fC->Column(var),
                          m_symbols->registerSymbol(varName));
            const FileContent* prevFile = previous->getFileContent();
            NodeId prevNode = previous->getNodeId();
            Location loc2(prevFile->getFileId(prevNode),
                          prevFile->Line(prevNode), prevFile->Column(prevNode),
                          m_symbols->registerSymbol(varName));
            Error err(ErrorDefinition::COMP_MULTIPLY_DEFINED_VARIABLE, loc1,
                      loc2);
            m_errors->addError(err);
          }

          Variable* variable = new Variable(datatype, fC, var, range, varName);
          parent->addVariable(variable);
        }

        variable_decl_assignment = fC->Sibling(variable_decl_assignment);
      }
    } else if (var_type == VObjectType::paType_declaration) {
      // compile_type_declaration_(fC, var_decl);
    }
  }

  return true;
}

VObjectType getSignalType(const FileContent* fC, NodeId net_port_type,
                          NodeId& Packed_dimension, bool& is_signed,
                          bool& is_var, NodeId& nodeType) {
  Packed_dimension = InvalidNodeId;
  is_signed = false;
  is_var = false;
  VObjectType signal_type = VObjectType::paData_type_or_implicit;
  if (net_port_type) {
    NodeId data_type_or_implicit = fC->Child(net_port_type);
    VObjectType the_type = fC->Type(data_type_or_implicit);
    if (the_type == VObjectType::paNetType_Wire ||
        the_type == VObjectType::paNetType_Wand ||
        the_type == VObjectType::paNetType_Uwire ||
        the_type == VObjectType::paNetType_Wor ||
        the_type == VObjectType::paNetType_Tri ||
        the_type == VObjectType::paNetType_TriAnd ||
        the_type == VObjectType::paNetType_TriOr ||
        the_type == VObjectType::paNetType_Tri1 ||
        the_type == VObjectType::paNetType_Tri0 ||
        the_type == VObjectType::paNetType_TriReg ||
        the_type == VObjectType::paNetType_Supply0 ||
        the_type == VObjectType::paNetType_Supply1 ||
        the_type == VObjectType::paImplicit_data_type) {
      signal_type = the_type;
      if (the_type == VObjectType::paImplicit_data_type) {
        // Interconnect
        Packed_dimension = fC->Child(data_type_or_implicit);
        if (fC->Type(Packed_dimension) == VObjectType::paSigning_Signed) {
          is_signed = true;
        }
        if (fC->Type(Packed_dimension) != VObjectType::paPacked_dimension) {
          Packed_dimension = InvalidNodeId;
        }
      }
      data_type_or_implicit = fC->Sibling(data_type_or_implicit);
      if (data_type_or_implicit) {
        Packed_dimension = fC->Child(data_type_or_implicit);
      }
    }
    NodeId data_type = fC->Child(data_type_or_implicit);
    if (data_type) {
      VObjectType the_type = fC->Type(data_type);
      if (the_type == VObjectType::paVar_type) {
        is_var = true;
        data_type_or_implicit = fC->Sibling(data_type);
        data_type = fC->Child(data_type_or_implicit);
        if (data_type)
          the_type = fC->Type(data_type);
        else
          nodeType = data_type_or_implicit;
      }
      if (the_type == VObjectType::paData_type) {
        NodeId integer_vector_type = fC->Child(data_type);
        the_type = fC->Type(integer_vector_type);
        if (the_type == VObjectType::paIntVec_TypeBit ||
            the_type == VObjectType::paIntVec_TypeLogic ||
            the_type == VObjectType::paIntVec_TypeReg ||
            the_type == VObjectType::slStringConst ||
            the_type == VObjectType::paClass_scope ||
            the_type == VObjectType::paIntegerAtomType_Int ||
            the_type == VObjectType::paIntegerAtomType_Integer ||
            the_type == VObjectType::paIntegerAtomType_Shortint ||
            the_type == VObjectType::paIntegerAtomType_LongInt ||
            the_type == VObjectType::paIntegerAtomType_Byte ||
            the_type == VObjectType::paString_type) {
          if (the_type == VObjectType::paIntegerAtomType_Int ||
              the_type == VObjectType::paIntegerAtomType_Shortint ||
              the_type == VObjectType::paIntegerAtomType_LongInt ||
              the_type == VObjectType::paIntegerAtomType_Byte ||
              the_type == VObjectType::paIntegerAtomType_Integer) {
            is_signed = true;
          }

          if (the_type == VObjectType::slStringConst) {
            const std::string_view tname = fC->SymName(integer_vector_type);
            if (tname == "logic") {
              the_type = VObjectType::paIntVec_TypeLogic;
            } else if (tname == "bit") {
              the_type = VObjectType::paIntVec_TypeBit;
            } else if (tname == "byte") {
              the_type = VObjectType::paIntegerAtomType_Byte;
              is_signed = true;
            }
          }
          signal_type = the_type;
          nodeType = integer_vector_type;
          if (the_type != VObjectType::paClass_scope)
            Packed_dimension = fC->Sibling(integer_vector_type);
          else
            Packed_dimension = fC->Sibling(fC->Sibling(integer_vector_type));
        }
      } else if (the_type == VObjectType::paSigning_Signed) {
        Packed_dimension = fC->Sibling(data_type);
        is_signed = true;
      } else if (the_type == VObjectType::paSigning_Unsigned) {
        Packed_dimension = fC->Sibling(data_type);
        is_signed = false;
      } else if (the_type == VObjectType::paPacked_dimension) {
        Packed_dimension = data_type;
      }

      if (fC->Type(Packed_dimension) == VObjectType::paSigning_Signed) {
        Packed_dimension = fC->Sibling(Packed_dimension);
        is_signed = true;
      } else if (fC->Type(Packed_dimension) ==
                 VObjectType::paSigning_Unsigned) {
        Packed_dimension = fC->Sibling(Packed_dimension);
        is_signed = false;
      }
    }
  }
  return signal_type;
}

void setDirectionAndType(DesignComponent* component, const FileContent* fC,
                         NodeId signal, VObjectType type,
                         VObjectType signal_type, NodeId packed_dimension,
                         bool is_signed, bool is_var, NodeId nodeType,
                         UHDM::VectorOfattribute* attributes) {
  ModuleDefinition* module =
      valuedcomponenti_cast<ModuleDefinition*>(component);
  VObjectType dir_type = VObjectType::slNoType;
  if (type == VObjectType::paInput_declaration)
    dir_type = VObjectType::paPortDir_Inp;
  else if (type == VObjectType::paOutput_declaration)
    dir_type = VObjectType::paPortDir_Out;
  else if (type == VObjectType::paInout_declaration)
    dir_type = VObjectType::paPortDir_Inout;

  if (module) {
    while (signal) {
      bool found = false;
      for (Signal* port : module->getPorts()) {
        std::string_view port_name = port->getName();
        if (port_name == fC->SymName(signal)) {
          found = true;
        }
        if (port->isExplicitlyNamed()) {
          if (fC->Type(port->getPortExpression()) ==
              VObjectType::slStringConst) {
            port_name = fC->SymName(port->getPortExpression());
          } else if (fC->Type(port->getPortExpression()) ==
                     VObjectType::paPort_expression) {
            NodeId Port_reference = fC->Child(port->getPortExpression());
            NodeId Actual = fC->Child(Port_reference);
            port_name = fC->SymName(Actual);
          }
        }
        if (port_name == fC->SymName(signal)) {
          port->setStatic();
          if (is_signed) port->setSigned();
          NodeId unpacked_dimension = fC->Sibling(signal);
          if (fC->Type(unpacked_dimension) ==
              VObjectType::paUnpacked_dimension) {
            port->setUnpackedDimension(unpacked_dimension);
          }
          if (fC->Type(unpacked_dimension) ==
              VObjectType::paConstant_expression) {
            port->setDefaultValue(unpacked_dimension);
          }
          if (attributes) port->attributes(attributes);
          port->setPackedDimension(packed_dimension);
          port->setDirection(dir_type);
          if (signal_type != VObjectType::paData_type_or_implicit) {
            port->setType(signal_type);
          }
          if (nodeType) {
            port->setTypespecId(nodeType);
          }
          if (is_var) port->setVar();
          break;
        }
      }
      if (found == false) {
        Signal* sig = new Signal(
            fC, signal, signal_type, packed_dimension, dir_type, nodeType,
            /* unpackedDimension */ InvalidNodeId, is_signed);
        sig->setStatic();
        if (is_var) sig->setVar();
        if (attributes) sig->attributes(attributes);
        component->getPorts().push_back(sig);
        component->getSignals().push_back(sig);
      }
      signal = fC->Sibling(signal);

      while (fC->Type(signal) == VObjectType::paVariable_dimension) {
        signal = fC->Sibling(signal);
      }

      if (fC->Type(signal) == VObjectType::paConstant_expression) {
        signal = fC->Sibling(signal);
      }

      if (fC->Type(signal) == VObjectType::paUnpacked_dimension) {
        break;
      }
    }
    return;
  }
  Program* program = valuedcomponenti_cast<Program*>(component);
  if (program) {
    while (signal) {
      for (auto& port : program->getPorts()) {
        if (port->getName() == fC->SymName(signal)) {
          port->setDirection(dir_type);
          if (signal_type != VObjectType::paData_type_or_implicit)
            port->setType(signal_type);
          break;
        }
      }
      signal = fC->Sibling(signal);
    }
  }
}

bool CompileHelper::compilePortDeclaration(DesignComponent* component,
                                           const FileContent* fC, NodeId id,
                                           CompileDesign* compileDesign,
                                           VObjectType& port_direction,
                                           bool hasNonNullPort) {
  VObjectType type = fC->Type(id);
  switch (type) {
    case VObjectType::paPort: {
      /*
        n<mem_if> u<3> t<StringConst> p<6> s<5> l<1>
        n<> u<4> t<Constant_bit_select> p<5> l<1>
        n<> u<5> t<Constant_select> p<6> c<4> l<1>
        n<> u<6> t<Port_reference> p<11> c<3> s<10> l<1>
        n<mif> u<7> t<StringConst> p<10> s<9> l<1>
        n<> u<8> t<Constant_bit_select> p<9> l<1>
        n<> u<9> t<Constant_select> p<10> c<8> l<1>
        n<> u<10> t<Port_reference> p<11> c<7> l<1>
        n<> u<11> t<Port_expression> p<12> c<6> l<1>
        n<> u<12> t<Port> p<13> c<11> l<1>
       */

      NodeId Port_expression = fC->Child(id);
      if (Port_expression &&
          (fC->Type(Port_expression) == VObjectType::paPort_expression)) {
        NodeId if_type = fC->Child(Port_expression);
        if (fC->Type(if_type) == VObjectType::paPort_reference) {
          NodeId if_type_name_s = fC->Child(if_type);
          NodeId if_name = fC->Sibling(if_type);
          if (if_name) {
            NodeId if_name_s = fC->Child(if_name);
            Signal* signal =
                new Signal(fC, if_name_s, if_type_name_s, VObjectType::slNoType,
                           InvalidNodeId, false);
            signal->setStatic();
            component->getPorts().push_back(signal);
          } else {
            Signal* signal = new Signal(fC, if_type_name_s,
                                        VObjectType::paData_type_or_implicit,
                                        port_direction, InvalidNodeId, false);
            signal->setStatic();
            component->getPorts().push_back(signal);
          }
        }
      } else if (Port_expression &&
                 (fC->Type(Port_expression) == VObjectType::slStringConst)) {
        // Non-ansi explicitly named port: mod (.X(int_name))
        NodeId explicitName = Port_expression;
        Port_expression = fC->Sibling(Port_expression);
        NodeId Port_reference = fC->Child(Port_expression);
        NodeId Actual = fC->Child(Port_reference);
        if (fC->Sibling(Port_reference)) {
          Actual = Port_expression;
        }
        Signal* signal = new Signal(fC, explicitName, Actual);
        signal->setExplicitlyNamed();
        component->getPorts().push_back(signal);
      } else {
        if (hasNonNullPort) {
          // Null port
          Signal* signal =
              new Signal(fC, id, VObjectType::slNoType, VObjectType::slNoType,
                         InvalidNodeId, false);
          signal->setStatic();
          component->getPorts().push_back(signal);
        }
      }
      break;
    }
    case VObjectType::paPort_declaration: {
      /*
          n<Configuration> u<21> t<StringConst> p<22> l<7>
          n<> u<22> t<Interface_identifier> p<26> c<21> s<25> l<7>
          n<cfg> u<23> t<StringConst> p<24> l<7>
          n<> u<24> t<Interface_identifier> p<25> c<23> l<7>
          n<> u<25> t<List_of_interface_identifiers> p<26> c<24> l<7>
          n<> u<26> t<Interface_port_declaration> p<27> c<22> l<7>
          n<> u<27> t<Port_declaration> p<28> c<26> l<7>
       */
      NodeId subNode = fC->Child(id);
      VObjectType subType = fC->Type(subNode);
      UHDM::VectorOfattribute* attributes = nullptr;
      if (subType == VObjectType::paAttribute_instance) {
        attributes =
            compileAttributes(component, fC, subNode, compileDesign, nullptr);
        while (fC->Type(subNode) == VObjectType::paAttribute_instance) {
          subNode = fC->Sibling(subNode);
          subType = fC->Type(subNode);
        }
      }
      switch (subType) {
        case VObjectType::paInterface_port_declaration: {
          /*
          n<DD2> u<12> t<StringConst> p<13> l<16>
          n<> u<13> t<Interface_identifier> p<17> c<12> s<16> l<16>
          n<toto2> u<14> t<StringConst> p<15> l<16>
          n<> u<15> t<Interface_identifier> p<16> c<14> l<16>
          n<> u<16> t<List_of_interface_identifiers> p<17> c<15> l<16>
          n<> u<17> t<Interface_port_declaration> p<18> c<13> l<16>
          n<> u<18> t<Port_declaration> p<19> c<17> l<16>
          */
          NodeId type_identifier = fC->Child(subNode);
          NodeId interfIdName = fC->Child(type_identifier);

          NodeId list_of_interface_identifiers = fC->Sibling(type_identifier);
          NodeId interface_identifier =
              fC->Child(list_of_interface_identifiers);
          while (interface_identifier) {
            NodeId identifier = fC->Child(interface_identifier);
            NodeId Unpacked_dimension = fC->Sibling(interface_identifier);
            NodeId unpackedDimension;
            if (fC->Type(Unpacked_dimension) ==
                VObjectType::paUnpacked_dimension) {
              interface_identifier = fC->Sibling(interface_identifier);
              unpackedDimension = Unpacked_dimension;
            }
            Signal* signal =
                new Signal(fC, identifier, interfIdName, VObjectType::slNoType,
                           unpackedDimension, false);
            signal->setStatic();
            component->getSignals().push_back(signal);
            interface_identifier = fC->Sibling(interface_identifier);
            while (interface_identifier &&
                   (fC->Type(interface_identifier) ==
                    VObjectType::paUnpacked_dimension)) {
              interface_identifier = fC->Sibling(interface_identifier);
            }
          }
          break;
        }
        case VObjectType::paAttribute_instance:
          /* module dff0_test(n1);
              (* init = 32'd1 *)
              output n1; */
          subNode = fC->Sibling(subNode);
          subType = fC->Type(subNode);
          [[fallthrough]];
        case VObjectType::paInput_declaration:
        case VObjectType::paOutput_declaration:
        case VObjectType::paInout_declaration: {
          /*
            n<> u<24> t<Data_type_or_implicit> p<25> l<7>
            n<> u<25> t<Net_port_type> p<28> c<24> s<27> l<7>
            n<c0> u<26> t<StringConst> p<27> l<7>
            n<> u<27> t<List_of_port_identifiers> p<28> c<26> l<7>
            n<> u<28> t<Output_declaration> p<29> c<25> l<7>
           */
          NodeId net_port_type = fC->Child(subNode);
          NodeId Packed_dimension;
          bool is_signed = false;
          bool is_var = false;
          NodeId nodeType;
          VObjectType signal_type = getSignalType(
              fC, net_port_type, /*ref*/ Packed_dimension,
              /*ref*/ is_signed, /*ref*/ is_var, /*ref*/ nodeType);
          NodeId list_of_port_identifiers = fC->Sibling(net_port_type);
          if (fC->Type(list_of_port_identifiers) ==
              VObjectType::paPacked_dimension) {
            list_of_port_identifiers = fC->Sibling(list_of_port_identifiers);
          }
          NodeId signal = fC->Child(list_of_port_identifiers);
          if (!nodeType) {
            nodeType = fC->Child(net_port_type);
          }
          setDirectionAndType(component, fC, signal, subType, signal_type,
                              Packed_dimension, is_signed, is_var, nodeType,
                              attributes);
          break;
        }
        default:
          break;
      }
      break;
    }
    default:
      break;
  }
  return true;
}

bool CompileHelper::compileAnsiPortDeclaration(DesignComponent* component,
                                               const FileContent* fC, NodeId id,
                                               VObjectType& port_direction) {
  /*
  n<mem_if> u<3> t<StringConst> p<4> l<11>
  n<> u<4> t<Data_type> p<5> c<3> l<11>
  n<> u<5> t<Data_type_or_implicit> p<6> c<4> l<11>
  n<> u<6> t<Net_port_type> p<7> c<5> l<11>
  n<> u<7> t<Net_port_header> p<9> c<6> s<8> l<11>
  n<sif1> u<8> t<StringConst> p<9> l<11>
  n<> u<9> t<Ansi_port_declaration> p<16> c<7> s<15> l<11>

  or

  n<> u<3> t<PortDir_Inp> p<7> s<6> l<1>
  n<> u<4> t<NetType_Wire> p<6> s<5> l<1>
  n<> u<5> t<Data_type_or_implicit> p<6> l<1>
  n<> u<6> t<Net_port_type> p<7> c<4> l<1>
  n<> u<7> t<Net_port_header> p<9> c<3> s<8> l<1>
  */

  NodeId net_port_header = fC->Child(id);
  NodeId identifier = fC->Sibling(net_port_header);
  NodeId net_port_type = fC->Child(net_port_header);
  VObjectType dir_type = fC->Type(net_port_type);
  if (dir_type == VObjectType::paPortDir_Out ||
      dir_type == VObjectType::paPortDir_Inp ||
      dir_type == VObjectType::paPortDir_Inout ||
      dir_type == VObjectType::paPortDir_Ref) {
    port_direction = dir_type;
    net_port_type = fC->Sibling(net_port_type);
    NodeId NetType = fC->Child(net_port_type);
    if (fC->Type(NetType) == VObjectType::paData_type_or_implicit) {
      NodeId Data_type = fC->Child(NetType);
      if (fC->Type(Data_type) == VObjectType::paData_type) {
        NetType = fC->Child(Data_type);
      }
    }

    NodeId packedDimension = fC->Sibling(NetType);
    if (fC->Type(packedDimension) ==
        VObjectType::slStringConst) {  // net type is class_scope
      packedDimension = fC->Sibling(packedDimension);
    }
    if (fC->Type(NetType) == VObjectType::paImplicit_data_type) {
      packedDimension = fC->Child(NetType);
      if (fC->Type(packedDimension) != VObjectType::paPacked_dimension) {
        packedDimension = InvalidNodeId;
      }
    }
    NodeId specParamId;
    bool is_signed = false;
    bool is_var = false;
    if (!packedDimension) {
      packedDimension = fC->Child(NetType);
    }

    if (fC->Type(packedDimension) == VObjectType::paSigning_Signed) {
      packedDimension = fC->Sibling(packedDimension);
    } else if (fC->Type(packedDimension) == VObjectType::paSigning_Unsigned) {
      packedDimension = fC->Sibling(packedDimension);
    }
    if (fC->Type(NetType) == VObjectType::paClass_scope) {
      specParamId = NetType;
    } else if (fC->Type(NetType) == VObjectType::slStringConst) {
      specParamId = NetType;
    }
    if (fC->Type(packedDimension) != VObjectType::paPacked_dimension) {
      packedDimension = InvalidNodeId;
    }

    NodeId nodeType;
    VObjectType signal_type =
        getSignalType(fC, net_port_type, /*ref*/ packedDimension,
                      /*ref*/ is_signed, /*ref*/ is_var, /*ref*/ nodeType);
    NodeId unpackedDimension;
    NodeId defaultValue;
    NodeId tmp = fC->Sibling(identifier);
    if (fC->Type(tmp) == VObjectType::paUnpacked_dimension) {
      unpackedDimension = tmp;
    }
    if (fC->Type(tmp) == VObjectType::paConstant_expression) {
      defaultValue = tmp;
      if (dir_type == VObjectType::paPortDir_Ref) {
        Location loc(fC->getFileId(tmp), fC->Line(tmp), fC->Column(tmp),
                     m_symbols->registerSymbol(fC->SymName(identifier)));
        Error err(ErrorDefinition::COMP_ILLEGAL_DEFAULT_PORT_VALUE, loc, loc);
        m_errors->addError(err);
      }
    }
    if (!nodeType) {
      nodeType = NetType;
    }
    Signal* p = new Signal(fC, identifier, signal_type, packedDimension,
                           port_direction, specParamId ? specParamId : nodeType,
                           unpackedDimension, is_signed);
    if (is_var) p->setVar();
    p->setDefaultValue(defaultValue);
    p->setStatic();
    component->getPorts().push_back(p);
    Signal* s = new Signal(fC, identifier, signal_type, packedDimension,
                           port_direction, specParamId ? specParamId : nodeType,
                           unpackedDimension, is_signed);
    if (is_var) s->setVar();
    s->setStatic();
    component->getSignals().push_back(s);
  } else if (dir_type == VObjectType::paInterface_identifier) {
    NodeId interface_port_header = net_port_header;
    NodeId interface_identifier = fC->Child(interface_port_header);
    NodeId interface_name = fC->Child(interface_identifier);
    NodeId port_name = fC->Sibling(interface_port_header);
    NodeId unpacked_dimension = fC->Sibling(port_name);
    /*
    n<mem_if> u<10> t<StringConst> p<12> s<11> l<11>
    n<system> u<11> t<StringConst> p<12> l<11>
    n<> u<12> t<Interface_identifier> p<13> c<10> l<11>
    n<> u<13> t<Interface_port_header> p<15> c<12> s<14> l<11>
    n<sif2> u<14> t<StringConst> p<15> l<11>
    n<> u<15> t<Ansi_port_declaration> p<16> c<13> l<11>
    */
    Signal* s = new Signal(fC, port_name, interface_name, VObjectType::slNoType,
                           unpacked_dimension, false);
    s->setStatic();
    s->setTypespecId(interface_name);
    component->getPorts().push_back(s);
  } else {
    NodeId data_type_or_implicit = fC->Child(net_port_type);
    NodeId data_type = fC->Child(data_type_or_implicit);
    if (data_type) {
      NodeId if_type_name_s = fC->Child(data_type);
      NodeId unpackedDimension = fC->Sibling(identifier);
      if (fC->Type(unpackedDimension) != VObjectType::paUnpacked_dimension)
        unpackedDimension = InvalidNodeId;
      if (fC->Type(if_type_name_s) == VObjectType::paIntVec_TypeReg ||
          fC->Type(if_type_name_s) == VObjectType::paIntVec_TypeLogic) {
        Signal* signal =
            new Signal(fC, identifier, fC->Type(if_type_name_s),
                       VObjectType::slNoType, unpackedDimension, false);
        signal->setStatic();
        component->getPorts().push_back(signal);
        // DO NOT create signals for interfaces:
        // component->getSignals().push_back(signal);
      } else {
        Signal* s = new Signal(fC, identifier, if_type_name_s,
                               VObjectType::slNoType, unpackedDimension, false);
        s->setStatic();
        s->setTypespecId(if_type_name_s);
        component->getPorts().push_back(s);
        // DO NOT create signals for interfaces:
        // component->getSignals().push_back(signal);
      }
    } else {
      VObjectType dataType = VObjectType::paData_type_or_implicit;
      NodeId packed;
      NodeId unpacked;
      bool is_signed = false;
      NodeId specParamId;
      // Reuse last signal data type (if any)
      Signal* last = nullptr;
      if (!component->getPorts().empty()) {
        last = component->getPorts().back();
        dataType = last->getType();
        packed = last->getPackedDimension();
        is_signed = last->isSigned();
        specParamId = last->getTypeSpecId();
        unpacked = last->getUnpackedDimension();
      }
      if (specParamId) {
        Signal* signal =
            new Signal(fC, identifier, dataType, packed, port_direction,
                       specParamId, unpacked, is_signed);
        signal->setStatic();
        component->getPorts().push_back(signal);
        signal = new Signal(fC, identifier, dataType, packed, port_direction,
                            specParamId, unpacked, is_signed);
        signal->setStatic();
        component->getSignals().push_back(signal);
      } else {
        if (fC->Type(net_port_header) == VObjectType::paInterface_port_header) {
          dataType = VObjectType::paInterface_port_header;
        }
        Signal* signal = new Signal(fC, identifier, dataType, port_direction,
                                    packed, is_signed);
        if (fC->Type(net_port_header) == VObjectType::paInterface_port_header) {
          signal->setTypespecId(identifier);
        }
        signal->setStatic();
        component->getPorts().push_back(signal);
        signal = new Signal(fC, identifier, dataType, port_direction, packed,
                            is_signed);
        if (fC->Type(net_port_header) == VObjectType::paInterface_port_header) {
          signal->setTypespecId(identifier);
        }
        signal->setStatic();
        component->getSignals().push_back(signal);
      }
    }
  }
  return true;
}

bool CompileHelper::compileNetDeclaration(DesignComponent* component,
                                          const FileContent* fC, NodeId id,
                                          bool interface,
                                          CompileDesign* compileDesign,
                                          UHDM::VectorOfattribute* attributes) {
  /*
 n<> u<17> t<NetType_Wire> p<18> l<27>
 n<> u<18> t<NetTypeOrTrireg_Net> p<22> c<17> s<21> l<27>
 n<a> u<19> t<StringConst> p<20> l<27>
 n<> u<20> t<Net_decl_assignment> p<21> c<19> l<27>
 n<> u<21> t<List_of_net_decl_assignments> p<22> c<20> l<27>
 n<> u<22> t<Net_declaration> p<23> c<18> l<27>
   */
  NodeId List_of_net_decl_assignments;
  NodeId Packed_dimension;
  bool isSigned = false;
  VObjectType nettype = VObjectType::slNoType;
  VObjectType subnettype = VObjectType::slNoType;
  NodeId NetTypeOrTrireg_Net = fC->Child(id);
  NodeId NetType = fC->Child(NetTypeOrTrireg_Net);
  if (!NetType) {
    NetType = NetTypeOrTrireg_Net;
    nettype = fC->Type(NetType);
    if (NetType) {
      if (fC->SymName(NetType) == "logic") {
        nettype = VObjectType::paIntVec_TypeLogic;
      }
    }
    NodeId Data_type_or_implicit = fC->Sibling(NetType);
    Packed_dimension = fC->Child(Data_type_or_implicit);
    if (fC->Type(Packed_dimension) == VObjectType::paSigning_Signed) {
      isSigned = true;
    }
    if (fC->Type(Data_type_or_implicit) == VObjectType::paData_type_or_implicit)
      List_of_net_decl_assignments = fC->Sibling(Data_type_or_implicit);
    else
      List_of_net_decl_assignments = Data_type_or_implicit;
  } else {
    nettype = fC->Type(NetType);
    NodeId net = fC->Sibling(NetTypeOrTrireg_Net);
    if (fC->Type(net) == VObjectType::paPacked_dimension) {
      List_of_net_decl_assignments = fC->Sibling(net);
    } else {
      List_of_net_decl_assignments = net;
    }
  }

  NodeId delay;
  if (fC->Type(List_of_net_decl_assignments) == VObjectType::paDelay3 ||
      fC->Type(List_of_net_decl_assignments) == VObjectType::paDelay_control) {
    delay = List_of_net_decl_assignments;
    List_of_net_decl_assignments = fC->Sibling(List_of_net_decl_assignments);
  }
  NodeId net_decl_assignment = fC->Child(List_of_net_decl_assignments);
  if (!net_decl_assignment) {
    net_decl_assignment = List_of_net_decl_assignments;
  }
  while (net_decl_assignment) {
    NodeId signal = fC->Child(net_decl_assignment);
    if (!signal) {
      signal = net_decl_assignment;
    }
    Signal* portRef = nullptr;
    for (auto& port : component->getPorts()) {
      if (port->getName() == fC->SymName(signal)) {
        port->setType(fC->Type(NetType));
        portRef = port;
        break;
      }
    }
    NodeId Unpacked_dimension;
    NodeId tmp = fC->Sibling(signal);
    if (fC->Type(tmp) == VObjectType::paUnpacked_dimension) {
      Unpacked_dimension = tmp;
    }

    if (fC->Type(Packed_dimension) == VObjectType::paData_type) {
      NetType = fC->Child(Packed_dimension);
      if (fC->Type(NetType) !=
          VObjectType::paIntVec_TypeLogic) {  //"wire logic" is "wire"
        subnettype = nettype;
        nettype = fC->Type(NetType);
      }
    }

    if (nettype == VObjectType::slStringConst) {
      Signal* sig = new Signal(fC, signal, InvalidNodeId, subnettype,
                               Unpacked_dimension, false);
      if (portRef) portRef->setLowConn(sig);
      sig->setDelay(delay);
      sig->setStatic();
      sig->setTypespecId(NetType);
      sig->attributes(attributes);
      if (isSigned) sig->setSigned();
      // Preserve the original net keyword (e.g. wand/wor) for typed net decls
      // like "wand typename". ElaborationStep may later overwrite m_type.
      if (subnettype != VObjectType::slNoType) sig->setSubNetType(subnettype);
      component->getSignals().push_back(sig);
    } else {
      Signal* sig =
          new Signal(fC, signal, nettype, Packed_dimension,
                     VObjectType::slNoType, NetType, Unpacked_dimension, false);
      if (portRef) portRef->setLowConn(sig);
      sig->setDelay(delay);
      sig->setStatic();
      sig->attributes(attributes);
      if (isSigned) sig->setSigned();
      // Preserve the original net keyword (e.g. wand/wor) for typed net decls
      // like "wand integer" where nettype was overwritten by the data type.
      if (subnettype != VObjectType::slNoType) sig->setSubNetType(subnettype);
      component->getSignals().push_back(sig);
    }

    net_decl_assignment = fC->Sibling(net_decl_assignment);
  }
  return true;
}

void CompileHelper::compileImportDeclaration(DesignComponent* component,
                                             const FileContent* fC,
                                             NodeId package_import_item_id,
                                             CompileDesign* compileDesign) {
  /*
     Verilog:
       import my_pkg::opcode_e, my_pkg::OPCODE_LOAD;
     Expected tree:
       n<my_pkg> u<27> t<StringConst> p<29> s<28> l<3>
       n<opcode_e> u<28> t<StringConst> p<29> l<3>
       n<> u<29> t<Package_import_item> p<33> c<27> s<32> l<3>
       n<my_pkg> u<30> t<StringConst> p<32> s<31> l<3>
       n<OPCODE_LOAD> u<31> t<StringConst> p<32> l<3>
       n<> u<32> t<Package_import_item> p<33> c<30> l<3>
       n<> u<33> t<Package_import_declaration> p<34> c<29> l<3>
     */
  Serializer& s = compileDesign->getSerializer();
  while (package_import_item_id) {
    import_typespec* import_stmt = s.MakeImport_typespec();
    fC->populateCoreMembers(package_import_item_id, package_import_item_id,
                            import_stmt);
    import_stmt->VpiName(fC->SymName(package_import_item_id));
    NodeId package_name_id = fC->Child(package_import_item_id);

    NodeId item_name_id = fC->Sibling(package_name_id);
    Value* item_name = m_exprBuilder.getValueFactory().newStValue();
    if (item_name_id) {
      item_name->set(fC->SymName(item_name_id));
    } else {
      item_name->set("*");
    }
    UHDM::constant* imported_item = constantFromValue(item_name, compileDesign);
    if (item_name_id) {
      // In case of "*" item_name_id will be 0
      fC->populateCoreMembers(item_name_id, item_name_id, imported_item);
    }
    m_exprBuilder.deleteValue(item_name);
    import_stmt->Item(imported_item);

    const std::string_view package_name = fC->SymName(package_name_id);
    import_stmt->VpiName(package_name);

    package_import_item_id = fC->Sibling(package_import_item_id);
    component->addImportedSymbol(import_stmt);
  }
}

bool CompileHelper::compileDataDeclaration(
    DesignComponent* component, const FileContent* fC, NodeId id,
    bool interface, CompileDesign* compileDesign, Reduce reduce,
    UHDM::VectorOfattribute* attributes) {
  NodeId subNode = fC->Child(id);
  VObjectType subType = fC->Type(subNode);
  switch (subType) {
    case VObjectType::paPackage_import_declaration:
      break;
    case VObjectType::paType_declaration:
    case VObjectType::paNet_type_declaration: {
      /*
        n<> u<15> t<Data_type> p<17> c<8> s<16> l<13>
        n<fsm_t> u<16> t<StringConst> p<17> l<13>
        n<> u<17> t<Type_declaration> p<18> c<15> l<13>
        n<> u<18> t<Data_declaration> p<19> c<17> l<13>
       */
      compileTypeDef(component, fC, id, compileDesign, reduce, nullptr);
      break;
    }
    default:
      /*
       n<> u<29> t<IntVec_TypeReg> p<30> l<29>
       n<> u<30> t<Data_type> p<34> c<29> s<33> l<29>
       n<b> u<31> t<StringConst> p<32> l<29>
       n<> u<32> t<Variable_decl_assignment> p<33> c<31> l<29>
       n<> u<33> t<List_of_variable_decl_assignments> p<34> c<32> l<29>
       n<> u<34> t<Variable_declaration> p<35> c<30> l<29>
       n<> u<35> t<Data_declaration> p<36> c<34> l<29>
       */
      NodeId data_decl = id;
      NodeId var_decl = fC->Child(data_decl);
      VObjectType type = fC->Type(data_decl);
      bool is_static = (valuedcomponenti_cast<ModuleDefinition*>(component) ||
                        valuedcomponenti_cast<Program*>(component));
      if (fC->Type(var_decl) == VObjectType::paLifetime_Automatic) {
        is_static = false;
        data_decl = fC->Sibling(var_decl);
        var_decl = data_decl;
      } else if (type == VObjectType::paData_declaration) {
        data_decl = fC->Child(data_decl);
        type = fC->Type(data_decl);
        var_decl = data_decl;
      }
      bool is_local = false;
      bool is_protected = false;
      bool is_rand = false;
      bool is_randc = false;
      bool is_const = false;
      bool is_signed = false;
      while ((type == VObjectType::paPropQualifier_ClassItem) ||
             (type == VObjectType::paPropQualifier_Rand) ||
             (type == VObjectType::paPropQualifier_Randc) ||
             (type == VObjectType::paConst_type) ||
             (type == VObjectType::paLifetime_Static)) {
        NodeId qualifier = fC->Child(data_decl);
        VObjectType qualType = fC->Type(qualifier);
        if (qualType == VObjectType::paClassItemQualifier_Protected)
          is_protected = true;
        if (qualType == VObjectType::paClassItemQualifier_Static)
          is_static = true;
        if (qualType == VObjectType::paClassItemQualifier_Local)
          is_local = true;
        if (type == VObjectType::paPropQualifier_Rand) is_rand = true;
        if (type == VObjectType::paPropQualifier_Randc) is_randc = true;
        if (type == VObjectType::paConst_type) is_const = true;
        if (type == VObjectType::paLifetime_Static) is_static = true;
        data_decl = fC->Sibling(data_decl);
        type = fC->Type(data_decl);
        var_decl = data_decl;
      }

      NodeId variable_declaration = var_decl;
      if (fC->Type(variable_declaration) == VObjectType::paData_declaration)
        variable_declaration = fC->Child(variable_declaration);
      bool var_type = false;
      if (fC->Type(variable_declaration) == VObjectType::paConst_type) {
        variable_declaration = fC->Sibling(variable_declaration);
        is_const = true;
      }
      if (fC->Type(variable_declaration) == VObjectType::paVar_type) {
        variable_declaration = fC->Sibling(variable_declaration);
        var_type = true;
      }
      NodeId data_type = fC->Child(variable_declaration);
      NodeId intVec_TypeReg = fC->Child(data_type);
      if (fC->Type(intVec_TypeReg) == VObjectType::paVIRTUAL)
        intVec_TypeReg = fC->Sibling(intVec_TypeReg);
      if (fC->Type(intVec_TypeReg) == VObjectType::paIntegerAtomType_Byte ||
          fC->Type(intVec_TypeReg) == VObjectType::paIntegerAtomType_Int ||
          fC->Type(intVec_TypeReg) == VObjectType::paIntegerAtomType_Integer ||
          fC->Type(intVec_TypeReg) == VObjectType::paIntegerAtomType_LongInt ||
          fC->Type(intVec_TypeReg) == VObjectType::paIntegerAtomType_Shortint ||
          fC->Type(intVec_TypeReg) == VObjectType::paReal_number) {
        is_signed = true;
      }
      NodeId packedDimension = fC->Sibling(intVec_TypeReg);
      if (fC->Type(packedDimension) == VObjectType::slStringConst) {
        // class or package name;
        if (fC->Type(fC->Sibling(packedDimension)) ==
            VObjectType::paPacked_dimension) {
          packedDimension = fC->Sibling(packedDimension);
        } else {
          packedDimension = InvalidNodeId;
        }
      } else if (fC->Type(packedDimension) == VObjectType::paSigning_Signed) {
        is_signed = true;
        packedDimension = fC->Sibling(packedDimension);
      } else if (fC->Type(packedDimension) == VObjectType::paSigning_Unsigned) {
        packedDimension = fC->Sibling(packedDimension);
        is_signed = false;
      }
      NodeId unpackedDimension;
      NodeId list_of_variable_decl_assignments = fC->Sibling(data_type);
      if (fC->Type(list_of_variable_decl_assignments) ==
          VObjectType::paPacked_dimension) {
        list_of_variable_decl_assignments =
            fC->Sibling(list_of_variable_decl_assignments);
      }
      NodeId variable_decl_assignment =
          fC->Child(list_of_variable_decl_assignments);
      while (variable_decl_assignment) {
        NodeId signal = fC->Child(variable_decl_assignment);
        Signal* portRef = nullptr;
        unpackedDimension = fC->Sibling(signal);
        for (Signal* port : component->getPorts()) {
          if (port->getName() == fC->SymName(signal)) {
            port->setType(fC->Type(intVec_TypeReg));
            portRef = port;
            break;
          }
        }
        Signal* sig = nullptr;
        VObjectType sigType = fC->Type(intVec_TypeReg);

        sig = new Signal(fC, signal, sigType, packedDimension,
                         VObjectType::slNoType, intVec_TypeReg,
                         unpackedDimension, false);

        if (is_const) sig->setConst();
        if (var_type) sig->setVar();
        if (portRef) portRef->setLowConn(sig);
        if (is_local) sig->setLocal();
        if (is_static) sig->setStatic();
        if (is_protected) sig->setProtected();
        if (is_rand) sig->setRand();
        if (is_randc) sig->setRandc();
        if (is_signed) sig->setSigned();
        sig->attributes(attributes);
        component->getSignals().push_back(sig);
        variable_decl_assignment = fC->Sibling(variable_decl_assignment);
      }
      break;
  }
  return true;
}

std::vector<cont_assign*> CompileHelper::compileContinuousAssignment(
    DesignComponent* component, const FileContent* fC,
    NodeId List_of_net_assignments, CompileDesign* compileDesign,
    ValuedComponentI* instance) {
  UHDM::Serializer& s = compileDesign->getSerializer();
  std::vector<cont_assign*> assigns;
  /*
n<o> u<6> t<StringConst> p<7> l<4>
n<> u<7> t<Ps_or_hierarchical_identifier> p<10> c<6> s<9> l<4>
n<> u<8> t<Constant_bit_select> p<9> l<4>
n<> u<9> t<Constant_select> p<10> c<8> l<4>
n<> u<10> t<Net_lvalue> p<15> c<7> s<14> l<4>
n<i> u<11> t<StringConst> p<12> l<4>
n<> u<12> t<Primary_literal> p<13> c<11> l<4>
n<> u<13> t<Primary> p<14> c<12> l<4>
n<> u<14> t<Expression> p<15> c<13> l<4>
n<> u<15> t<Net_assignment> p<16> c<10> l<4>
n<> u<16> t<List_of_net_assignments> p<17> c<15> l<4>
n<> u<17> t<Continuous_assign> p<18> c<16> l<4>
*/
  NodeId Strength0;
  NodeId Strength1;
  expr* delay_expr = nullptr;
  // NodeId List_of_net_assignments = fC->Child(id);
  if (fC->Type(List_of_net_assignments) == VObjectType::paDrive_strength) {
    NodeId Drive_strength = List_of_net_assignments;
    Strength0 = fC->Child(Drive_strength);
    Strength1 = fC->Sibling(Strength0);
    List_of_net_assignments = fC->Sibling(List_of_net_assignments);
  } else if (fC->Type(List_of_net_assignments) == VObjectType::paDelay3) {
    delay_expr =
        (expr*)compileExpression(component, fC, List_of_net_assignments,
                                 compileDesign, Reduce::No, nullptr, instance);
    List_of_net_assignments = fC->Sibling(List_of_net_assignments);
  }
  NodeId Net_assignment = fC->Child(List_of_net_assignments);
  while (Net_assignment) {
    NodeId Net_lvalue = fC->Child(Net_assignment);
    NodeId Expression = fC->Sibling(Net_lvalue);
    if (Expression &&
        (fC->Type(Expression) != VObjectType::paUnpacked_dimension)) {
      // LHS
      NodeId Ps_or_hierarchical_identifier = fC->Child(Net_lvalue);
      NodeId Hierarchical_identifier = Ps_or_hierarchical_identifier;
      if (fC->Type(fC->Child(Ps_or_hierarchical_identifier)) ==
          VObjectType::paHierarchical_identifier) {
        Hierarchical_identifier = fC->Child(fC->Child(Hierarchical_identifier));
      }
      UHDM::any* lhs_exp =
          compileExpression(component, fC, Hierarchical_identifier,
                            compileDesign, Reduce::No, nullptr, instance);
      NodeId Constant_select = fC->Sibling(Ps_or_hierarchical_identifier);
      if ((fC->Type(Constant_select) == VObjectType::paConstant_select) &&
          (Ps_or_hierarchical_identifier != Hierarchical_identifier) &&
          (lhs_exp->UhdmType() == uhdmhier_path)) {
        if (UHDM::any* sel = compileSelectExpression(
                component, fC, fC->Child(Constant_select), "", compileDesign,
                Reduce::No, lhs_exp, instance, false)) {
          hier_path* path = (hier_path*)lhs_exp;
          any* last = path->Path_elems()->back();
          if (last->UhdmType() == uhdmref_obj &&
              sel->UhdmType() == uhdmbit_select) {
            ref_obj* last_ro = (ref_obj*)last;
            bit_select* sel_bs = (bit_select*)sel;
            path->Path_elems()->pop_back();
            sel_bs->VpiName(last->VpiName());
            sel_bs->VpiFullName(
                StrCat(last_ro->VpiFullName(), decompileHelper(sel)));
          }
          path->Path_elems()->push_back(sel);
          std::string path_name(path->VpiName());
          path_name += decompileHelper(sel);
          path->VpiName(path_name);
          path->VpiFullName(path_name);
        }
      }

      UHDM::cont_assign* cassign = s.MakeCont_assign();

      // RHS
      UHDM::any* rhs_exp =
          compileExpression(component, fC, Expression, compileDesign,
                            Reduce::No, cassign, instance);

      if (Strength0) {
        VObjectType st0 = fC->Type(Strength0);
        if (st0 == VObjectType::paSUPPLY0 || st0 == VObjectType::paSTRONG0 ||
            st0 == VObjectType::paPULL0 || st0 == VObjectType::paWEAK0 ||
            st0 == VObjectType::paHIGHZ0) {
          cassign->VpiStrength0(
              UhdmWriter::getStrengthType(fC->Type(Strength0)));
        } else {
          cassign->VpiStrength1(
              UhdmWriter::getStrengthType(fC->Type(Strength0)));
        }
      }
      if (Strength1) {
        VObjectType st1 = fC->Type(Strength1);
        if (st1 == VObjectType::paSUPPLY0 || st1 == VObjectType::paSTRONG0 ||
            st1 == VObjectType::paPULL0 || st1 == VObjectType::paWEAK0 ||
            st1 == VObjectType::paHIGHZ0) {
          cassign->VpiStrength0(
              UhdmWriter::getStrengthType(fC->Type(Strength1)));
        } else {
          cassign->VpiStrength1(
              UhdmWriter::getStrengthType(fC->Type(Strength1)));
        }
      }
      if (delay_expr != nullptr) {
        delay_expr->VpiParent(cassign);
        cassign->Delay(delay_expr);
      }

      cassign->Lhs((UHDM::expr*)lhs_exp);
      cassign->Rhs((UHDM::expr*)rhs_exp);
      setParentNoOverride(lhs_exp, cassign);
      setParentNoOverride(rhs_exp, cassign);
      fC->populateCoreMembers(List_of_net_assignments, List_of_net_assignments,
                              cassign);
      assigns.push_back(cassign);
    }
    Net_assignment = fC->Sibling(Net_assignment);
  }
  return assigns;
}

std::string CompileHelper::decompileHelper(const any* sel) {
  std::string path_name;
  UHDM::ExprEval eval;
  if (sel == nullptr) {
    return "";
  }
  if (sel->UhdmType() == uhdmconstant) {
    const std::string_view ind = ((expr*)sel)->VpiDecompile();
    path_name.append(ind);
  } else if (sel->UhdmType() == uhdmref_obj) {
    const std::string_view ind = ((expr*)sel)->VpiName();
    path_name.append(ind);
  } else if (sel->UhdmType() == uhdmoperation) {
    path_name.append(eval.prettyPrint(sel));
  } else if (sel->UhdmType() == uhdmbit_select) {
    bit_select* bsel = (bit_select*)sel;
    const expr* index = bsel->VpiIndex();
    if (index->UhdmType() == uhdmconstant) {
      const std::string_view ind = ((expr*)index)->VpiDecompile();
      path_name.append("[").append(ind).append("]");
    } else if (index->UhdmType() == uhdmref_obj) {
      const std::string_view ind = ((expr*)index)->VpiName();
      path_name.append("[").append(ind).append("]");
    } else if (index->UhdmType() == uhdmoperation) {
      path_name.append("[" + eval.prettyPrint(index) + "]");
    }
  } else if (const part_select* pselect = any_cast<const part_select*>(sel)) {
    std::string selectRange =
        StrCat("[", decompileHelper(pselect->Left_range()), ":",
               decompileHelper(pselect->Right_range()), "]");
    path_name += selectRange;
  } else if (const indexed_part_select* pselect =
                 any_cast<const indexed_part_select*>(sel)) {
    std::string selectRange = StrCat(
        "[", decompileHelper(pselect->Base_expr()),
        ((pselect->VpiIndexedPartSelectType() == vpiPosIndexed) ? "+" : "-"),
        ":", decompileHelper(pselect->Width_expr()), "]");
    path_name += selectRange;
  } else if (const var_select* pselect = any_cast<const var_select*>(sel)) {
    std::string selectRange;
    VectorOfexpr* exprs = pselect->Exprs();
    for (auto ex : *exprs) {
      std::string tmp = decompileHelper(ex);
      if ((!tmp.empty()) && tmp[0] != '[') selectRange += StrCat("[");
      selectRange += StrCat(tmp);
      if ((!tmp.empty()) && tmp[0] != '[') selectRange += StrCat("]");
    }
    path_name += selectRange;
  }
  return path_name;
}

std::pair<std::vector<UHDM::module_array*>, std::vector<UHDM::ref_module*>>
CompileHelper::compileInstantiation(ModuleDefinition* mod,
                                    const FileContent* fC,
                                    CompileDesign* compileDesign, NodeId id,
                                    ValuedComponentI* instance) {
  std::pair<std::vector<UHDM::module_array*>, std::vector<UHDM::ref_module*>>
      results;
  UHDM::Serializer& s = compileDesign->getSerializer();
  NodeId moduleName = fC->sl_collect(id, VObjectType::slStringConst);
  const std::string_view libName = fC->getLibrary()->getName();
  const std::string_view mname = fC->SymName(moduleName);
  std::string modName = StrCat(libName, "@", mname);

  NodeId typespecId = fC->Child(id);
  NodeId hierInstId = fC->sl_collect(id, VObjectType::paHierarchical_instance);
  while (hierInstId) {
    NodeId instId = fC->sl_collect(hierInstId, VObjectType::paName_of_instance);
    NodeId identifierId;
    std::string instName;
    if (instId) {
      identifierId = fC->Child(instId);
      instName = fC->SymName(identifierId);
    }

    NodeId unpackedDimId = fC->Sibling(identifierId);
    if (unpackedDimId) {
      int32_t unpackedSize = 0;
      if (std::vector<UHDM::range*>* unpackedDimensions =
              compileRanges(mod, fC, unpackedDimId, compileDesign, Reduce::No,
                            nullptr, instance, unpackedSize, false)) {
        UHDM::module_array* mod_array = s.MakeModule_array();
        mod_array->Ranges(unpackedDimensions);
        mod_array->VpiName(instName);
        mod_array->VpiFullName(modName);
        fC->populateCoreMembers(identifierId, identifierId, mod_array);
        for (auto r : *unpackedDimensions) r->VpiParent(mod_array);

        module_typespec* tps = s.MakeModule_typespec();
        tps->VpiName(fC->SymName(typespecId));
        fC->populateCoreMembers(typespecId, typespecId, tps);
        if (mod_array->Elem_typespec() == nullptr) {
          ref_typespec* tpsRef = s.MakeRef_typespec();
          tpsRef->VpiParent(mod_array);
          mod_array->Elem_typespec(tpsRef);
        }
        mod_array->Elem_typespec()->Actual_typespec(tps);
        tps->VpiParent(mod_array);
        VectorOfport* ports = s.MakePortVec();
        mod_array->Ports(ports);
        compileHighConn(mod, fC, compileDesign, instId, ports);
        for (auto p : *ports) p->VpiParent(mod_array);
        results.first.push_back(mod_array);
      }
    } else {
      // Simple instance
      UHDM::ref_module* m = s.MakeRef_module();
      m->VpiName(instName);
      m->VpiDefName(modName);
      fC->populateCoreMembers(identifierId, identifierId, m);
      VectorOfport* ports = s.MakePortVec();
      m->Ports(ports);
      results.second.push_back(m);
      compileHighConn(mod, fC, compileDesign, instId, ports);
      for (auto p : *ports) p->VpiParent(m);
    }
    hierInstId = fC->Sibling(hierInstId);
  }
  return results;
}

uint32_t CompileHelper::getBuiltinType(VObjectType type) {
  switch (type) {
    case VObjectType::paNInpGate_And:
      return vpiAndPrim;
    case VObjectType::paNInpGate_Or:
      return vpiOrPrim;
    case VObjectType::paNInpGate_Nor:
      return vpiNorPrim;
    case VObjectType::paNInpGate_Nand:
      return vpiNandPrim;
    case VObjectType::paNInpGate_Xor:
      return vpiXorPrim;
    case VObjectType::paNInpGate_Xnor:
      return vpiXnorPrim;
    case VObjectType::paNOutGate_Buf:
      return vpiBufPrim;
    case VObjectType::paNOutGate_Not:
      return vpiNotPrim;
    case VObjectType::paPassEnSwitch_Tranif0:
      return vpiTranif0Prim;
    case VObjectType::paPassEnSwitch_Tranif1:
      return vpiTranif1Prim;
    case VObjectType::paPassEnSwitch_RTranif1:
      return vpiRtranif1Prim;
    case VObjectType::paPassEnSwitch_RTranif0:
      return vpiRtranif0Prim;
    case VObjectType::paPassSwitch_Tran:
      return vpiTranPrim;
    case VObjectType::paPassSwitch_RTran:
      return vpiRtranPrim;
    case VObjectType::paCmosSwitchType_Cmos:
      return vpiCmosPrim;
    case VObjectType::paCmosSwitchType_RCmos:
      return vpiRcmosPrim;
    case VObjectType::paEnableGateType_Bufif0:
      return vpiBufif0Prim;
    case VObjectType::paEnableGateType_Bufif1:
      return vpiBufif1Prim;
    case VObjectType::paEnableGateType_Notif0:
      return vpiNotif0Prim;
    case VObjectType::paEnableGateType_Notif1:
      return vpiNotif1Prim;
    case VObjectType::paMosSwitchType_NMos:
      return vpiNmosPrim;
    case VObjectType::paMosSwitchType_PMos:
      return vpiPmosPrim;
    case VObjectType::paMosSwitchType_RNMos:
      return vpiRnmosPrim;
    case VObjectType::paMosSwitchType_RPMos:
      return vpiRpmosPrim;
    case VObjectType::paPULLUP:
      return vpiPullupPrim;
    case VObjectType::paPULLDOWN:
      return vpiPulldownPrim;
    default:
      return 0;
  }
}

void CompileHelper::compileUdpInstantiation(ModuleDefinition* mod,
                                            const FileContent* fC,
                                            CompileDesign* compileDesign,
                                            NodeId id,
                                            ValuedComponentI* instance) {
  VObjectTypeUnorderedSet insttypes = {VObjectType::paUdp_instance};
  UHDM::Serializer& s = compileDesign->getSerializer();
  std::vector<NodeId> hierInstIds = fC->sl_collect_all(id, insttypes, true);
  NodeId hierInstId;
  if (!hierInstIds.empty()) hierInstId = hierInstIds[0];
  NodeId udpDefId = fC->Child(id);
  if (!hierInstId) return;
  std::string_view instName;
  while (hierInstId) {
    NodeId instId = fC->sl_collect(hierInstId, VObjectType::paName_of_instance);
    NodeId identifierId;
    NodeId Net_lvalue;
    if (instId) {
      identifierId = fC->Child(instId);
      instName = fC->SymName(identifierId);
      Net_lvalue = fC->Sibling(instId);
    }

    NodeId unpackedDimId;
    if (identifierId) unpackedDimId = fC->Sibling(identifierId);
    UHDM::udp* udp = s.MakeUdp();
    UHDM::primitive* gate = udp;
    if (unpackedDimId &&
        (fC->Type(unpackedDimId) == VObjectType::paUnpacked_dimension)) {
      // Vector instances
      int32_t size;
      VectorOfrange* ranges =
          compileRanges(mod, fC, unpackedDimId, compileDesign, Reduce::No,
                        nullptr, instance, size, false);
      if (mod->getPrimitiveArrays() == nullptr) {
        mod->setPrimitiveArrays(s.MakePrimitive_arrayVec());
      }
      UHDM::primitive_array* gate_array = s.MakeUdp_array();
      VectorOfprimitive* prims = s.MakePrimitiveVec();
      gate_array->Primitives(prims);
      gate_array->Ranges(ranges);
      prims->push_back(gate);
      mod->getPrimitiveArrays()->push_back(gate_array);
    } else {
      if (mod->getPrimitives() == nullptr) {
        mod->setPrimitives(s.MakePrimitiveVec());
      }
      mod->getPrimitives()->push_back(gate);
    }

    gate->VpiName(instName);
    gate->VpiDefName(fC->SymName(udpDefId));
    fC->populateCoreMembers(id, id, gate);
    writePrimTerms(mod, fC, compileDesign, Net_lvalue, gate, 0, instance);
    hierInstId = fC->Sibling(hierInstId);
  }
}

void CompileHelper::writePrimTerms(ModuleDefinition* mod, const FileContent* fC,
                                   CompileDesign* compileDesign, NodeId id,
                                   primitive* prim, int32_t vpiGateType,
                                   ValuedComponentI* instance) {
  UHDM::Serializer& s = compileDesign->getSerializer();
  VectorOfprim_term* terms = s.MakePrim_termVec();
  prim->Prim_terms(terms);
  uint32_t index = 0;
  while (id) {
    prim_term* term = s.MakePrim_term();
    terms->push_back(term);
    NodeId expId = fC->Child(id);
    expr* hconn = (expr*)compileExpression(mod, fC, expId, compileDesign,
                                           Reduce::No, nullptr);
    hconn->VpiParent(prim);
    term->Expr(hconn);
    fC->populateCoreMembers(id, id, term);
    term->VpiParent(prim);
    term->VpiTermIndex(index);
    if (vpiGateType == vpiBufPrim || vpiGateType == vpiNotPrim) {
      if (index == 0) {
        term->VpiDirection(vpiOutput);
      } else {
        term->VpiDirection(vpiInput);
      }
    } else if (vpiGateType == vpiTranif1Prim || vpiGateType == vpiTranif0Prim ||
               vpiGateType == vpiRtranif1Prim ||
               vpiGateType == vpiRtranif0Prim || vpiGateType == vpiTranPrim ||
               vpiGateType == vpiRtranPrim) {
      if (index == 0) {
        term->VpiDirection(vpiInout);
      } else {
        term->VpiDirection(vpiInput);
      }
    } else {
      if (index == 0) {
        term->VpiDirection(vpiOutput);
      } else {
        term->VpiDirection(vpiInput);
      }
    }
    index++;

    id = fC->Sibling(id);
  }
}

void CompileHelper::compileGateInstantiation(ModuleDefinition* mod,
                                             const FileContent* fC,
                                             CompileDesign* compileDesign,
                                             NodeId id,
                                             ValuedComponentI* instance) {
  UHDM::Serializer& s = compileDesign->getSerializer();
  UHDM::primitive* gate = nullptr;
  UHDM::primitive_array* gate_array = nullptr;
  NodeId gatenode = fC->Child(fC->Parent(id));
  VObjectType gatetype = fC->Type(gatenode);
  int32_t vpiGateType = getBuiltinType(gatetype);
  NodeId Name_of_instance = fC->Child(id);
  NodeId Name = fC->Child(Name_of_instance);
  NodeId Unpacked_dimension = fC->Sibling(Name);
  if (vpiGateType == vpiPmosPrim || vpiGateType == vpiRpmosPrim ||
      vpiGateType == vpiNmosPrim || vpiGateType == vpiRnmosPrim ||
      vpiGateType == vpiCmosPrim || vpiGateType == vpiRcmosPrim ||
      vpiGateType == vpiTranif1Prim || vpiGateType == vpiTranif0Prim ||
      vpiGateType == vpiRtranif1Prim || vpiGateType == vpiRtranif0Prim ||
      vpiGateType == vpiTranPrim || vpiGateType == vpiRtranPrim) {
    gate = s.MakeSwitch_tran();
    if (fC->Type(Unpacked_dimension) == VObjectType::paUnpacked_dimension) {
      gate_array = s.MakeSwitch_array();
      VectorOfprimitive* prims = s.MakePrimitiveVec();
      int32_t size;
      VectorOfrange* ranges =
          compileRanges(mod, fC, Unpacked_dimension, compileDesign, Reduce::No,
                        nullptr, instance, size, false);
      gate_array->Primitives(prims);
      gate_array->Ranges(ranges);
      prims->push_back(gate);
      if (mod->getPrimitiveArrays() == nullptr) {
        mod->setPrimitiveArrays(s.MakePrimitive_arrayVec());
      }
      mod->getPrimitiveArrays()->push_back(gate_array);
    } else {
      if (mod->getPrimitives() == nullptr) {
        mod->setPrimitives(s.MakePrimitiveVec());
      }
      mod->getPrimitives()->push_back(gate);
    }
    gate->VpiPrimType(vpiGateType);
  } else {
    gate = s.MakeGate();
    if (fC->Type(Unpacked_dimension) == VObjectType::paUnpacked_dimension) {
      gate_array = s.MakeGate_array();
      gate_array->VpiName(fC->SymName(Name));
      fC->populateCoreMembers(id, id, gate_array);
      VectorOfprimitive* prims = s.MakePrimitiveVec();
      gate_array->Primitives(prims);
      int32_t size;
      if (VectorOfrange* ranges =
              compileRanges(mod, fC, Unpacked_dimension, compileDesign,
                            Reduce::No, gate_array, instance, size, false)) {
        gate_array->Ranges(ranges);
      }
      gate->VpiParent(gate_array);
      prims->push_back(gate);
      if (mod->getPrimitiveArrays() == nullptr) {
        mod->setPrimitiveArrays(s.MakePrimitive_arrayVec());
      }
      mod->getPrimitiveArrays()->push_back(gate_array);
    } else {
      if (mod->getPrimitives() == nullptr) {
        mod->setPrimitives(s.MakePrimitiveVec());
      }
      mod->getPrimitives()->push_back(gate);
    }

    gate->VpiPrimType(vpiGateType);
  }
  /*
  if (UHDM::VectorOfexpr* delays = child->getNetlist()->delays()) {
    if (delays->size() == 1) {
      gate->Delay((*delays)[0]);
    }
  }
  */
  if (gate) {
    gate->VpiName(fC->SymName(Name));
    gate->VpiDefName(UhdmWriter::builtinGateName(gatetype));
    fC->populateCoreMembers(id, id, gate);
  }
  NodeId Net_lvalue = fC->Sibling(Name_of_instance);
  writePrimTerms(mod, fC, compileDesign, Net_lvalue, gate, vpiGateType,
                 instance);
}

void CompileHelper::compileHighConn(ModuleDefinition* component,
                                    const FileContent* fC,
                                    CompileDesign* compileDesign, NodeId instId,
                                    VectorOfport* ports) {
  NodeId list_of_ports = fC->Sibling(instId);
  UHDM::Serializer& s = compileDesign->getSerializer();
  NodeId Port_connection = fC->Child(list_of_ports);

  while (Port_connection) {
    if (fC->Type(Port_connection) == VObjectType::paOrdered_port_connection) {
      NodeId child = fC->Child(Port_connection);
      if (child) {
        port* p = s.MakePort();
        ports->push_back(p);
        fC->populateCoreMembers(Port_connection, Port_connection, p);
        checkForLoops(true);
        if (any* exp = compileExpression(component, fC, child, compileDesign,
                                         Reduce::No, p, nullptr)) {
          p->High_conn(exp);
        }
        checkForLoops(false);
      }  // else:  mod inst ();
    } else if (fC->Type(Port_connection) ==
               VObjectType::paNamed_port_connection) {
      NodeId formalName = fC->Child(Port_connection);
      if (fC->Type(formalName) == VObjectType::paAttribute_instance) {
        formalName = fC->Sibling(formalName);
      }
      if (fC->Type(formalName) == VObjectType::paDOTSTAR) {
        constant* c = s.MakeConstant();
        c->VpiValue("STRING:.*");
        c->VpiDecompile(".*");
        fC->populateCoreMembers(Port_connection, Port_connection, c);
        port* p = s.MakePort();
        fC->populateCoreMembers(Port_connection, Port_connection, p);
        p->High_conn(c);
        c->VpiParent(p);
        ports->push_back(p);
      } else {
        NodeId openParens = fC->Sibling(formalName);
        NodeId expId = fC->Sibling(openParens);
        port* p = s.MakePort();
        ports->push_back(p);
        fC->populateCoreMembers(Port_connection, Port_connection, p);
        if (fC->Type(expId) == VObjectType::paCLOSE_PARENS) {
          // (.p())
        } else {
          p->VpiName(fC->SymName(formalName));
          if (expId) {  // (.p, ...)
            checkForLoops(true);
            if (any* exp =
                    compileExpression(component, fC, expId, compileDesign,
                                      Reduce::No, p, nullptr)) {
              p->High_conn(exp);
            }
            checkForLoops(false);
          }
        }
      }
    }
    Port_connection = fC->Sibling(Port_connection);
  }
}

initial* CompileHelper::compileInitialBlock(DesignComponent* component,
                                            const FileContent* fC,
                                            NodeId initial_construct,
                                            CompileDesign* compileDesign) {
  UHDM::Serializer& s = compileDesign->getSerializer();
  compileDesign->lockSerializer();
  initial* init = s.MakeInitial();
  fC->populateCoreMembers(initial_construct, initial_construct, init);
  NodeId Statement_or_null = fC->Child(initial_construct);
  if (VectorOfany* stmts = compileStmt(component, fC, Statement_or_null,
                                       compileDesign, Reduce::No, init)) {
    init->Stmt((*stmts)[0]);
  }
  compileDesign->unlockSerializer();
  return init;
}

final_stmt* CompileHelper::compileFinalBlock(DesignComponent* component,
                                             const FileContent* fC,
                                             NodeId final_construct,
                                             CompileDesign* compileDesign) {
  UHDM::Serializer& s = compileDesign->getSerializer();
  compileDesign->lockSerializer();
  final_stmt* final = s.MakeFinal_stmt();
  fC->populateCoreMembers(final_construct, final_construct, final);
  NodeId Statement_or_null = fC->Child(final_construct);
  if (VectorOfany* stmts = compileStmt(component, fC, Statement_or_null,
                                       compileDesign, Reduce::No, final)) {
    final->Stmt((*stmts)[0]);
  }
  compileDesign->unlockSerializer();
  return final;
}

UHDM::atomic_stmt* CompileHelper::compileProceduralTimingControlStmt(
    DesignComponent* component, const FileContent* fC,
    NodeId Procedural_timing_control, CompileDesign* compileDesign,
    UHDM::any* pstmt, ValuedComponentI* instance) {
  UHDM::Serializer& s = compileDesign->getSerializer();
  /*
  n<#100> u<70> t<IntConst> p<71> l<7>
  n<> u<71> t<Delay_control> p<72> c<70> l<7>
  n<> u<72> t<Procedural_timing_control> p<88> c<71> s<87> l<7>
  */

  NodeId Delay_control = fC->Child(Procedural_timing_control);
  if (fC->Type(Delay_control) == VObjectType::paEvent_control) {
    return compileEventControlStmt(component, fC, Procedural_timing_control,
                                   compileDesign, pstmt, instance);
  }
  NodeId IntConst = fC->Child(Delay_control);
  const std::string_view value = fC->SymName(IntConst);
  UHDM::delay_control* dc = s.MakeDelay_control();
  if (value[0] == '#') {
    dc->VpiDelay(value);
  } else {
    ref_obj* ref = s.MakeRef_obj();
    ref->VpiName(value);
    ref->VpiParent(pstmt);
    fC->populateCoreMembers(IntConst, IntConst, ref);
    dc->Delay(ref);
  }
  fC->populateCoreMembers(Delay_control, Delay_control, dc);
  NodeId Statement_or_null = fC->Sibling(Procedural_timing_control);
  if (Statement_or_null) {
    VectorOfany* st = compileStmt(component, fC, Statement_or_null,
                                  compileDesign, Reduce::No, dc, instance);
    if (st) {
      any* stmt = (*st)[0];
      dc->Stmt(stmt);
      stmt->VpiParent(dc);
    } else {
      // Malformed AST due to grammar for: #1 t
      NodeId unit = fC->Child(IntConst);
      if (unit) {
        unit = fC->Child(unit);  // StringConst child of Instance_name
        const std::string_view name = fC->SymName(unit);
        std::pair<task_func*, DesignComponent*> ret =
            getTaskFunc(name, component, compileDesign, nullptr, nullptr);
        task_func* tf = ret.first;
        any* call = nullptr;
        if (tf) {
          if (tf->UhdmType() == uhdmfunction) {
            func_call* fcall = s.MakeFunc_call();
            fcall->Function(any_cast<function*>(tf));
            call = fcall;
          } else {
            task_call* tcall = s.MakeTask_call();
            tcall->Task(any_cast<task*>(tf));
            call = tcall;
          }
        }
        if (call) {
          fC->populateCoreMembers(fC->Child(unit), fC->Child(unit), call);
          dc->Stmt(call);
          call->VpiParent(dc);
        }
      }
    }
  }
  return dc;
}

UHDM::atomic_stmt* CompileHelper::compileDelayControl(
    DesignComponent* component, const FileContent* fC,
    NodeId Procedural_timing_control, CompileDesign* compileDesign,
    UHDM::any* pexpr, ValuedComponentI* instance) {
  UHDM::Serializer& s = compileDesign->getSerializer();

  NodeId Delay_control = fC->Child(Procedural_timing_control);
  if (fC->Type(Delay_control) == VObjectType::paEvent_control) {
    return compileEventControlStmt(component, fC, Procedural_timing_control,
                                   compileDesign, pexpr, instance);
  }
  NodeId IntConst = fC->Child(Delay_control);
  const std::string_view value = fC->SymName(IntConst);
  UHDM::delay_control* dc = s.MakeDelay_control();
  dc->VpiDelay(value);
  dc->VpiParent(pexpr);
  fC->populateCoreMembers(fC->Child(Delay_control), fC->Child(Delay_control),
                          dc);
  return dc;
}

always* CompileHelper::compileAlwaysBlock(DesignComponent* component,
                                          const FileContent* fC, NodeId id,
                                          CompileDesign* compileDesign,
                                          ValuedComponentI* instance) {
  UHDM::Serializer& s = compileDesign->getSerializer();
  compileDesign->lockSerializer();
  always* always = s.MakeAlways();
  NodeId always_keyword = fC->Child(id);
  switch (fC->Type(always_keyword)) {
    case VObjectType::paALWAYS:
      always->VpiAlwaysType(vpiAlways);
      break;
    case VObjectType::paALWAYS_COMB:
      always->VpiAlwaysType(vpiAlwaysComb);
      break;
    case VObjectType::paALWAYS_FF:
      always->VpiAlwaysType(vpiAlwaysFF);
      break;
    case VObjectType::paALWAYS_LATCH:
      always->VpiAlwaysType(vpiAlwaysLatch);
      break;
    default:
      break;
  }
  NodeId Statement = fC->Sibling(always_keyword);
  NodeId Statement_item = fC->Child(Statement);
  VectorOfany* stmts = nullptr;
  if (fC->Type(Statement_item) == VObjectType::slStringConst) {
    stmts = compileStmt(component, fC, Statement_item, compileDesign,
                        Reduce::No, always, instance);
  } else {
    NodeId the_stmt = fC->Child(Statement_item);
    stmts = compileStmt(component, fC, the_stmt, compileDesign, Reduce::No,
                        always, instance);
  }
  if (stmts) {
    any* stmt = (*stmts)[0];
    always->Stmt(stmt);
    stmt->VpiParent(always);
  }

  fC->populateCoreMembers(id, id, always);
  compileDesign->unlockSerializer();
  return always;
}

bool CompileHelper::isMultidimensional(UHDM::typespec* ts,
                                       DesignComponent* component) {
  bool isMultiDimension = false;
  if (ts) {
    UHDM_OBJECT_TYPE ttps = ts->UhdmType();
    if (ttps == uhdmlogic_typespec) {
      logic_typespec* lts = (logic_typespec*)ts;
      if (lts->Ranges() && lts->Ranges()->size() > 1) isMultiDimension = true;
    } else if (ttps == uhdmarray_typespec) {
      array_typespec* lts = (array_typespec*)ts;
      if (lts->Ranges() && lts->Ranges()->size() > 1) isMultiDimension = true;
    } else if (ttps == uhdmpacked_array_typespec) {
      packed_array_typespec* lts = (packed_array_typespec*)ts;
      if (lts->Elem_typespec() && lts->Elem_typespec()->Actual_typespec() &&
          (lts->Elem_typespec()->Actual_typespec()->UhdmType() ==
           uhdmstruct_typespec)) {
        isMultiDimension = true;
      } else {
        if (lts->Ranges() && lts->Ranges()->size() > 1) isMultiDimension = true;
      }
    } else if (ttps == uhdmbit_typespec) {
      bit_typespec* lts = (bit_typespec*)ts;
      if (lts->Ranges() && lts->Ranges()->size() > 1) isMultiDimension = true;
    } else if (ttps == uhdmstruct_typespec) {
      // isMultiDimension = true;
    }
  }
  return isMultiDimension;
}

bool CompileHelper::isDecreasingRange(UHDM::typespec* ts,
                                      DesignComponent* component) {
  if (ts) {
    UHDM_OBJECT_TYPE ttps = ts->UhdmType();
    range* r = nullptr;
    if (ttps == uhdmlogic_typespec) {
      logic_typespec* lts = (logic_typespec*)ts;
      if (lts->Ranges() && !lts->Ranges()->empty()) {
        r = (*lts->Ranges())[0];
      }
    } else if (ttps == uhdmarray_typespec) {
      array_typespec* lts = (array_typespec*)ts;
      if (lts->Ranges() && !lts->Ranges()->empty()) {
        r = (*lts->Ranges())[0];
      }
    } else if (ttps == uhdmpacked_array_typespec) {
      packed_array_typespec* lts = (packed_array_typespec*)ts;
      if (lts->Ranges() && !lts->Ranges()->empty()) {
        r = (*lts->Ranges())[0];
      }
    } else if (ttps == uhdmbit_typespec) {
      bit_typespec* lts = (bit_typespec*)ts;
      if (lts->Ranges() && !lts->Ranges()->empty()) {
        r = (*lts->Ranges())[0];
      }
    }
    if (r) {
      bool invalidValue = false;
      UHDM::ExprEval eval;
      int64_t lv = eval.get_value(invalidValue, r->Left_expr());
      int64_t rv = eval.get_value(invalidValue, r->Right_expr());
      if ((invalidValue == false) && (lv > rv)) return true;
    }
  }
  return false;
}

UHDM::any* CompileHelper::defaultPatternAssignment(const UHDM::typespec* tps,
                                                   UHDM::any* exp,
                                                   DesignComponent* component,
                                                   CompileDesign* compileDesign,
                                                   ValuedComponentI* instance) {
  any* result = exp;
  if (tps == nullptr) {
    return result;
  }
  if (exp == nullptr) {
    return result;
  }
  UHDM::Serializer& s = compileDesign->getSerializer();
  FileSystem* const fileSystem = FileSystem::getInstance();
  bool invalidValue = false;
  int32_t ncsize = 32;
  range* r = nullptr;
  UHDM_OBJECT_TYPE ttps = tps->UhdmType();
  UHDM_OBJECT_TYPE baseType = uhdmint_typespec;
  if (ttps == uhdmlogic_typespec) {
    logic_typespec* lts = (logic_typespec*)tps;
    baseType = uhdmlogic_typespec;
    if (lts->Ranges() && !lts->Ranges()->empty()) {
      r = (*lts->Ranges())[0];
    }
    ncsize = 1;
  } else if (ttps == uhdmarray_typespec) {
    array_typespec* lts = (array_typespec*)tps;
    typespec* ets = nullptr;
    if (ref_typespec* rt = lts->Elem_typespec()) {
      ets = rt->Actual_typespec();
    }
    if (ets != nullptr) {
      baseType = ets->UhdmType();
      if (lts->Ranges() && !lts->Ranges()->empty()) {
        r = (*lts->Ranges())[0];
      }
      ncsize = Bits(
          ets, invalidValue, component, compileDesign, Reduce::Yes, instance,
          fileSystem->toPathId(ets->VpiFile(),
                               compileDesign->getCompiler()->getSymbolTable()),
          ets->VpiLineNo(), false);
    }
  } else if (ttps == uhdmpacked_array_typespec) {
    packed_array_typespec* lts = (packed_array_typespec*)tps;
    typespec* ets = nullptr;
    if (ref_typespec* rt = lts->Elem_typespec()) {
      ets = rt->Actual_typespec();
    }
    if (ets != nullptr) {
      baseType = ets->UhdmType();
      if (lts->Ranges() && !lts->Ranges()->empty()) {
        r = (*lts->Ranges())[0];
      }
      ncsize = Bits(
          ets, invalidValue, component, compileDesign, Reduce::Yes, instance,
          fileSystem->toPathId(ets->VpiFile(),
                               compileDesign->getCompiler()->getSymbolTable()),
          ets->VpiLineNo(), false);
    }
  } else if (ttps == uhdmbit_typespec) {
    bit_typespec* lts = (bit_typespec*)tps;
    baseType = uhdmbit_typespec;
    if (lts->Ranges() && !lts->Ranges()->empty()) {
      r = (*lts->Ranges())[0];
    }
    ncsize = 1;
  } else if (ttps == uhdmint_typespec) {
    ncsize = 32;
  } else if (ttps == uhdminteger_typespec) {
    ncsize = 32;
  } else if (ttps == uhdmshort_int_typespec) {
    ncsize = 16;
  } else if (ttps == uhdmbyte_typespec) {
    ncsize = 8;
  }

  if (exp->UhdmType() == uhdmoperation) {
    operation* op = (operation*)exp;
    VectorOfany* operands = op->Operands();
    int32_t opType = op->VpiOpType();
    switch (opType) {
      case vpiCastOp: {
        const typespec* optps = nullptr;
        if (const ref_typespec* rt = op->Typespec()) {
          optps = rt->Actual_typespec();
        }
        if (optps == nullptr) break;
        UHDM_OBJECT_TYPE ottps = optps->UhdmType();
        any* op0 = (*operands)[0];
        if (op0->UhdmType() == uhdmoperation) {
          operation* oper0 = (operation*)op0;
          int32_t op0Type = oper0->VpiOpType();
          if (op0Type == vpiConcatOp) {
            VectorOfany* operandsConcat = oper0->Operands();
            any* op0Concat = (*operandsConcat)[0];
            if (op0Concat->VpiName() == "default") {
              bool invalidValue = false;
              UHDM::ExprEval eval;
              uint64_t val0 =
                  eval.get_value(invalidValue, (expr*)(*operandsConcat)[1]);
              constant* c = s.MakeConstant();
              if (ottps == uhdmint_typespec) {
                int_typespec* itps = (int_typespec*)optps;
                if (itps->VpiSigned()) {
                  if (val0 == 1) {
                    c->VpiDecompile(std::to_string(-1));
                    c->VpiValue("INT:" + std::to_string(-1));
                    c->VpiSize(32);
                    c->VpiConstType(vpiIntConst);
                    result = c;
                  } else {
                    c->VpiDecompile(std::to_string(0));
                    c->VpiValue("INT:" + std::to_string(0));
                    c->VpiSize(32);
                    c->VpiConstType(vpiIntConst);
                    result = c;
                  }
                } else {
                  if (val0 == 1) {
                    c->VpiDecompile(std::to_string(UINT_MAX));
                    c->VpiValue("UINT:" + std::to_string(UINT_MAX));
                    c->VpiSize(32);
                    c->VpiConstType(vpiUIntConst);
                    result = c;
                  } else {
                    c->VpiDecompile(std::to_string(0));
                    c->VpiValue("UINT:" + std::to_string(0));
                    c->VpiSize(32);
                    c->VpiConstType(vpiUIntConst);
                    result = c;
                  }
                }
              }
            }
          }
        }
        break;
      }
      case vpiAssignmentPatternOp: {
        any* op0 = (*operands)[0];
        if (op0->UhdmType() == uhdmtagged_pattern) {
          tagged_pattern* pattern = (tagged_pattern*)op0;
          const typespec* ptps = nullptr;
          if (const UHDM::ref_typespec* rt = pattern->Typespec()) {
            ptps = rt->Actual_typespec();
          }
          if (ptps->VpiName() == "default") {
            UHDM::ExprEval eval;
            expr* expat = (expr*)pattern->Pattern();
            constant* c = any_cast<constant*>(expat);
            int32_t psize = expat->VpiSize();
            if (psize == -1) {
              adjustUnsized(c, ncsize);
              c->VpiSize(ncsize);
            } else {
              if (ncsize < c->VpiSize()) c->VpiSize(ncsize);
            }
            if (r) {
              bool invalidValue = false;
              UHDM::ExprEval eval;
              expr* lexp = reduceExpr(
                  r->Left_expr(), invalidValue, component, compileDesign,
                  instance,
                  fileSystem->toPathId(
                      r->VpiFile(),
                      compileDesign->getCompiler()->getSymbolTable()),
                  r->VpiLineNo(), nullptr);
              expr* rexp = reduceExpr(
                  r->Right_expr(), invalidValue, component, compileDesign,
                  instance,
                  fileSystem->toPathId(
                      r->VpiFile(),
                      compileDesign->getCompiler()->getSymbolTable()),
                  r->VpiLineNo(), nullptr);
              uint64_t lv = eval.get_uvalue(invalidValue, lexp);
              uint64_t rv = eval.get_uvalue(invalidValue, rexp);
              if (invalidValue == false) {
                uint32_t max = std::max(lv, rv);
                uint32_t min = std::min(lv, rv);
                uint32_t size = max - min + 1;
                if (baseType == uhdmint_typespec) {
                  array_expr* array = s.MakeArray_expr();
                  VectorOfexpr* exprs = s.MakeExprVec();
                  array->Exprs(exprs);
                  for (uint32_t i = 0; i < size; i++) {
                    exprs->push_back(c);
                  }
                  result = array;
                }
              }
            }
          }
        }
        break;
      }
      case vpiMultiAssignmentPatternOp: {
        any* op1 = operands->at(1);
        if (op1->UhdmType() == uhdmoperation) {
          operation* oper = (operation*)op1;
          if (oper->VpiOpType() == vpiConcatOp) {
            VectorOfany* opers = oper->Operands();
            constant* c = any_cast<constant*>(opers->at(0));
            if (c) {
              int32_t psize = c->VpiSize();
              if (psize == -1) {
                adjustUnsized(c, ncsize);
                c->VpiSize(ncsize);
              }
            }
          }
        }
        break;
      }
      default:
        break;
    }
  }

  return result;
}

bool CompileHelper::compileParameterDeclaration(
    DesignComponent* component, const FileContent* fC, NodeId nodeId,
    CompileDesign* compileDesign, Reduce reduce, bool localParam,
    ValuedComponentI* instance, bool port_param, bool muteErrors) {
  UHDM::Serializer& s = compileDesign->getSerializer();
  compileDesign->lockSerializer();
  std::vector<UHDM::any*>* parameters = component->getParameters();
  if (parameters == nullptr) {
    component->setParameters(s.MakeAnyVec());
    parameters = component->getParameters();
  }
  UHDM::VectorOfparam_assign* param_assigns = component->getParam_assigns();
  if (param_assigns == nullptr) {
    component->setParam_assigns(s.MakeParam_assignVec());
    param_assigns = component->getParam_assigns();
  }
  if (fC->Type(nodeId) == VObjectType::paList_of_type_assignments) {
    // Type param
    NodeId typeNameId = fC->Child(nodeId);
    while (typeNameId) {
      NodeId ntype = fC->Sibling(typeNameId);
      bool skip = false;
      if (ntype && fC->Type(ntype) == VObjectType::paData_type) {
        ntype = fC->Child(ntype);
        if (fC->Type(ntype) == VObjectType::paVIRTUAL)
          ntype = fC->Sibling(ntype);
        skip = true;
      } else {
        ntype = InvalidNodeId;
      }
      UHDM::type_parameter* p = s.MakeType_parameter();
      p->VpiName(fC->SymName(typeNameId));
      fC->populateCoreMembers(typeNameId, typeNameId, p);
      if (typespec* tps = compileTypespec(component, fC, ntype, compileDesign,
                                          Reduce::No, p, nullptr, false)) {
        if (p->Typespec() == nullptr) {
          ref_typespec* tpsRef = s.MakeRef_typespec();
          tpsRef->VpiParent(p);
          p->Typespec(tpsRef);
        }
        p->Typespec()->Actual_typespec(tps);
        tps->VpiParent(p);
      }
      if (localParam) {
        p->VpiLocalParam(true);
      }
      parameters->push_back(p);
      Parameter* param = new Parameter(fC, typeNameId, fC->SymName(typeNameId),
                                       ntype, port_param);
      param->setTypeParam();
      param->setUhdmParam(p);
      component->insertParameter(param);
      typeNameId = fC->Sibling(typeNameId);
      if (skip) typeNameId = fC->Sibling(typeNameId);
    }

  } else if (fC->Type(nodeId) == VObjectType::paTYPE) {
    // Type param
    NodeId list_of_param_assignments = fC->Sibling(nodeId);
    NodeId Param_assignment = fC->Child(list_of_param_assignments);
    while (Param_assignment) {
      NodeId Identifier = fC->Child(Param_assignment);
      NodeId Constant_param_expression = fC->Sibling(Identifier);
      UHDM::type_parameter* p = s.MakeType_parameter();
      p->VpiName(fC->SymName(Identifier));
      fC->populateCoreMembers(Identifier, Identifier, p);
      NodeId Data_type = fC->Child(Constant_param_expression);
      if (typespec* tps =
              compileTypespec(component, fC, Data_type, compileDesign,
                              Reduce::No, p, nullptr, false)) {
        if (p->Typespec() == nullptr) {
          ref_typespec* tpsRef = s.MakeRef_typespec();
          tpsRef->VpiParent(p);
          p->Typespec(tpsRef);
        }
        p->Typespec()->Actual_typespec(tps);
        tps->VpiParent(p);
      }
      if (localParam) {
        p->VpiLocalParam(true);
      }
      parameters->push_back(p);
      Parameter* param = new Parameter(fC, Identifier, fC->SymName(Identifier),
                                       Constant_param_expression, port_param);
      param->setTypeParam();
      param->setUhdmParam(p);
      component->insertParameter(param);
      Param_assignment = fC->Sibling(Param_assignment);
    }
  } else {
    // Regular param
    NodeId Data_type_or_implicit;
    NodeId List_of_param_assignments;
    if (fC->Type(nodeId) == VObjectType::paList_of_param_assignments) {
      List_of_param_assignments = nodeId;
    } else {
      Data_type_or_implicit = fC->Child(nodeId);
      List_of_param_assignments = fC->Sibling(Data_type_or_implicit);
    }

    NodeId Param_assignment = fC->Child(List_of_param_assignments);
    while (Param_assignment) {
      UHDM::typespec* ts = nullptr;
      if (Data_type_or_implicit) {
        ts = compileTypespec(component, fC, fC->Child(Data_type_or_implicit),
                             compileDesign, reduce, nullptr, instance, false);
      }
      bool isSigned = false;
      NodeId Data_type = fC->Child(Data_type_or_implicit);
      VObjectType the_type = fC->Type(Data_type);
      if (the_type == VObjectType::paData_type) {
        Data_type = fC->Child(Data_type);
        NodeId Signage = fC->Sibling(Data_type);
        VObjectType type = fC->Type(Data_type);
        if (type == VObjectType::paIntegerAtomType_Byte ||
            type == VObjectType::paIntegerAtomType_Int ||
            type == VObjectType::paIntegerAtomType_Integer ||
            type == VObjectType::paIntegerAtomType_LongInt ||
            type == VObjectType::paIntegerAtomType_Shortint ||
            type == VObjectType::paReal_number) {
          isSigned = true;
        }
        if (fC->Type(Signage) == VObjectType::paSigning_Signed) isSigned = true;
        if (fC->Type(Signage) == VObjectType::paSigning_Unsigned)
          isSigned = false;
      }

      bool isMultiDimension = isMultidimensional(ts, component);
      bool isDecreasing = isDecreasingRange(ts, component);

      NodeId name = fC->Child(Param_assignment);
      NodeId value = fC->Sibling(name);

      UHDM::parameter* param = s.MakeParameter();
      Parameter* p =
          new Parameter(fC, name, fC->SymName(name),
                        fC->Child(Data_type_or_implicit), port_param);

      // Unpacked dimensions
      if (fC->Type(value) == VObjectType::paUnpacked_dimension) {
        int32_t unpackedSize;
        std::vector<UHDM::range*>* unpackedDimensions =
            compileRanges(component, fC, value, compileDesign, reduce, param,
                          instance, unpackedSize, muteErrors);
        param->Ranges(unpackedDimensions);
        param->VpiSize(unpackedSize);
        array_typespec* atps = s.MakeArray_typespec();
        ref_typespec* tsRef = s.MakeRef_typespec();
        tsRef->VpiParent(atps);
        tsRef->Actual_typespec(ts);
        atps->Elem_typespec(tsRef);
        ref_typespec* atpsRef = s.MakeRef_typespec();
        atpsRef->VpiParent(param);
        atpsRef->Actual_typespec(atps);
        param->Typespec(atpsRef);
        p->setTypespec(atps);
        fC->populateCoreMembers(Data_type_or_implicit,
                                value ? value : Data_type_or_implicit, atps);
        atps->Ranges(unpackedDimensions);
        while (fC->Type(value) == VObjectType::paUnpacked_dimension) {
          value = fC->Sibling(value);
        }
        ts = atps;
        isMultiDimension = true;
      }

      const std::string_view the_name = fC->SymName(name);
      NodeId actual_value = value;

      if ((valuedcomponenti_cast<Package*>(component) ||
           valuedcomponenti_cast<FileContent*>(component)) &&
          (instance == nullptr)) {
        if (!isMultiDimension) {
          // Check the RHS, we don't want to
          NodeId pattAssign = fC->sl_collect(
              actual_value, VObjectType::paConstant_concatenation);
          if (pattAssign != InvalidNodeId) {
            if (!compileDesign->getCompiler()
                     ->getCommandLineParser()
                     ->reportNonSynthesizable()) {
              // More constant pushing with Synth option on
              isMultiDimension = true;
            }
          }
        }
        UHDM::any* expr = compileExpression(
            component, fC, actual_value, compileDesign,
            isMultiDimension ? Reduce::No : reduce, param, nullptr);
        UHDM::UHDM_OBJECT_TYPE exprtype = expr->UhdmType();
        if (expr) {
          expr = defaultPatternAssignment(ts, expr, component, compileDesign,
                                          instance);
          exprtype = expr->UhdmType();
        }
        if (expr && exprtype == UHDM::uhdmarray_expr) {
          component->setComplexValue(the_name, (UHDM::expr*)expr);
        } else if (expr && exprtype == UHDM::uhdmconstant) {
          UHDM::constant* c = (UHDM::constant*)expr;
          if (c->Typespec() == nullptr) {
            ref_typespec* tsRef = s.MakeRef_typespec();
            tsRef->VpiParent(c);
            tsRef->Actual_typespec(ts);
            c->Typespec(tsRef);
          }
          int32_t size = c->VpiSize();
          if (ts) {
            bool invalidValue = false;
            int32_t sizetmp =
                Bits(ts, invalidValue, component, compileDesign, Reduce::Yes,
                     instance, fC->getFileId(), fC->Line(actual_value), false);
            if (!invalidValue) size = sizetmp;
          }
          adjustSize(ts, component, compileDesign, instance, c);
          Value* val = m_exprBuilder.fromVpiValue(c->VpiValue(), size);
          component->setValue(the_name, val, m_exprBuilder);
        } else if ((reduce == Reduce::Yes) && (!isMultiDimension)) {
          UHDM::expr* the_expr = (UHDM::expr*)expr;
          if (the_expr->Typespec() == nullptr) {
            ref_typespec* tsRef = s.MakeRef_typespec();
            tsRef->VpiParent(the_expr);
            tsRef->Actual_typespec(ts);
            the_expr->Typespec(tsRef);
          }
          ExprEval expr_eval(the_expr, instance, fC->getFileId(),
                             fC->Line(name), nullptr);
          component->scheduleParamExprEval(the_name, expr_eval);
        } else if (expr && ((exprtype == uhdmoperation) ||
                            (exprtype == uhdmfunc_call) ||
                            (exprtype == uhdmsys_func_call))) {
          component->setComplexValue(the_name, (UHDM::expr*)expr);
          UHDM::expr* the_expr = (UHDM::expr*)expr;
          if (the_expr->Typespec() == nullptr) {
            ref_typespec* tsRef = s.MakeRef_typespec();
            tsRef->VpiParent(the_expr);
            tsRef->Actual_typespec(ts);
            the_expr->Typespec(tsRef);
          }
          if (isDecreasing && (expr->UhdmType() == uhdmoperation)) {
            operation* op = (operation*)expr;
            int32_t optype = op->VpiOpType();
            if (optype == vpiAssignmentPatternOp || optype == vpiConcatOp) {
              VectorOfany* operands = op->Operands();
              if (operands && !operands->empty()) {
                if ((*operands)[0]->UhdmType() == uhdmref_obj) {
                  op->VpiReordered(true);
                  std::reverse(operands->begin(), operands->end());
                }
              }
            }
          }
        } else if (Value* val = m_exprBuilder.evalExpr(
                       fC, actual_value,
                       component)) {  // This call to create an error
          component->setValue(the_name, val, m_exprBuilder);
        }
      }
      p->setUhdmParam(param);
      p->setTypespec(ts);
      if (isMultiDimension) p->setMultidimension();
      component->insertParameter(p);

      if (ts) {
        if (param->Typespec() == nullptr) {
          ref_typespec* tsRef = s.MakeRef_typespec();
          tsRef->VpiParent(param);
          param->Typespec(tsRef);
        }
        param->Typespec()->Actual_typespec(ts);
        ts->VpiParent(param);
        if (ts->UhdmType() == uhdmunsupported_typespec) {
          component->needLateTypedefBinding(param);
        }
      }
      param->VpiSigned(isSigned);
      fC->populateCoreMembers(name, name, param);
      param->VpiName(fC->SymName(name));

      if (localParam) {
        param->VpiLocalParam(true);
      }
      parameters->push_back(param);

      ParamAssign* assign =
          new ParamAssign(fC, name, value, isMultiDimension, port_param);
      UHDM::param_assign* param_assign = s.MakeParam_assign();
      assign->setUhdmParamAssign(param_assign);
      component->addParamAssign(assign);
      fC->populateCoreMembers(Param_assignment, Param_assignment, param_assign);
      param_assigns->push_back(param_assign);
      if (param) {
        param_assign->Lhs(param);
        param->VpiParent(param_assign);
      }

      if (value) {
        // Unelaborated parameters
        if ((valuedcomponenti_cast<Package*>(component) ||
             valuedcomponenti_cast<FileContent*>(component)) &&
            (instance == nullptr)) {
          expr* rhs =
              (expr*)compileExpression(component, fC, value, compileDesign,
                                       Reduce::No, param_assign, instance);
          rhs = (expr*)defaultPatternAssignment(ts, rhs, component,
                                                compileDesign, instance);
          UHDM::param_assign* param_assign = s.MakeParam_assign();
          fC->populateCoreMembers(Param_assignment, Param_assignment,
                                  param_assign);
          ElaboratorContext elaboratorContext(&s, false, true);
          any* pclone = UHDM::clone_tree(param, &elaboratorContext);
          param_assign->Lhs(pclone);
          if (rhs != nullptr) {
            rhs->VpiParent(param_assign);
            param_assign->Rhs(rhs);
          }
          UHDM::VectorOfparam_assign* param_assigns =
              component->getOrigParam_assigns();
          if (param_assigns == nullptr) {
            component->setOrigParam_assigns(s.MakeParam_assignVec());
            param_assigns = component->getOrigParam_assigns();
          }
          param_assigns->push_back(param_assign);
        }

        expr* rhs = (expr*)compileExpression(
            component, fC, value, compileDesign,
            isMultiDimension ? Reduce::No : reduce, param_assign, instance);
        if (reduce == Reduce::Yes) {
          rhs = (expr*)defaultPatternAssignment(ts, rhs, component,
                                                compileDesign, instance);
        }
        if (isDecreasing) {
          if (rhs->UhdmType() == uhdmoperation) {
            operation* op = (operation*)rhs;
            int32_t optype = op->VpiOpType();
            if (optype == vpiAssignmentPatternOp || optype == vpiConcatOp) {
              VectorOfany* operands = op->Operands();
              if (operands && !operands->empty()) {
                if ((*operands)[0]->UhdmType() == uhdmref_obj) {
                  op->VpiReordered(true);
                  std::reverse(operands->begin(), operands->end());
                }
              }
            }
          }
        }
        if (rhs && (rhs->UhdmType() == uhdmconstant)) {
          constant* c = (constant*)rhs;
          if (ts == nullptr) {
            switch (c->VpiConstType()) {
              case vpiRealConst: {
                ts = s.MakeReal_typespec();
                p->setTypespec(ts);
                if (param->Typespec() == nullptr) {
                  ref_typespec* tsRef = s.MakeRef_typespec();
                  tsRef->VpiParent(param);
                  param->Typespec(tsRef);
                }
                param->Typespec()->Actual_typespec(ts);
                break;
              }
              case vpiDecConst: {
                break;
              }
              case vpiIntConst: {
                int_typespec* its = s.MakeInt_typespec();
                its->VpiSigned(false);
                fC->populateCoreMembers(nodeId, nodeId, its);
                const std::string_view v = c->VpiValue();
                if (v.front() == '-') {
                  its->VpiSigned(true);
                }
                ts = its;
                p->setTypespec(ts);
                if (param->Typespec() == nullptr) {
                  ref_typespec* tsRef = s.MakeRef_typespec();
                  tsRef->VpiParent(param);
                  param->Typespec(tsRef);
                }
                param->Typespec()->Actual_typespec(ts);
                break;
              }
              case vpiHexConst:
              case vpiOctConst:
              case vpiBinaryConst: {
                int_typespec* its = s.MakeInt_typespec();
                its->VpiSigned(false);
                fC->populateCoreMembers(nodeId, nodeId, its);
                if (c->VpiSize() != -1) {  // Unsized
                  range* r = s.MakeRange();
                  constant* l = s.MakeConstant();
                  l->VpiValue("INT:" + std::to_string(c->VpiSize() - 1));
                  r->Left_expr(l);
                  constant* rv = s.MakeConstant();
                  rv->VpiValue(std::string("INT:0"));
                  r->Right_expr(rv);
                  r->VpiParent(its);
                  VectorOfrange* ranges = s.MakeRangeVec();
                  ranges->push_back(r);
                  its->Ranges(ranges);

                  ts = its;
                  p->setTypespec(ts);

                  if (param->Typespec() == nullptr) {
                    ref_typespec* tsRef = s.MakeRef_typespec();
                    tsRef->VpiParent(param);
                    param->Typespec(tsRef);
                  }
                  param->Typespec()->Actual_typespec(ts);
                }
                break;
              }
              case vpiUIntConst: {
                int_typespec* its = s.MakeInt_typespec();
                fC->populateCoreMembers(nodeId, nodeId, its);
                its->VpiSigned(false);
                ts = its;
                p->setTypespec(ts);
                if (param->Typespec() == nullptr) {
                  ref_typespec* tsRef = s.MakeRef_typespec();
                  tsRef->VpiParent(param);
                  param->Typespec(tsRef);
                }
                param->Typespec()->Actual_typespec(ts);
                break;
              }
              case vpiStringConst: {
                ts = s.MakeString_typespec();
                p->setTypespec(ts);
                if (param->Typespec() == nullptr) {
                  ref_typespec* tsRef = s.MakeRef_typespec();
                  tsRef->VpiParent(param);
                  param->Typespec(tsRef);
                }
                param->Typespec()->Actual_typespec(ts);
                break;
              }
              default:
                break;
            }
          }
          if (reduce == Reduce::Yes)
            adjustSize(ts, component, compileDesign, instance, c);

          int32_t size = c->VpiSize();
          if (ts) {
            if (c->Typespec() == nullptr) {
              ref_typespec* tsRef = s.MakeRef_typespec();
              tsRef->VpiParent(c);
              c->Typespec(tsRef);
            }
            c->Typespec()->Actual_typespec(ts);

            if (reduce == Reduce::Yes) {
              bool invalidValue = false;
              int32_t sizetmp = Bits(ts, invalidValue, component, compileDesign,
                                     Reduce::Yes, instance, fC->getFileId(),
                                     fC->Line(actual_value), false);
              if (!invalidValue) size = sizetmp;
            }
          }
          if (rhs->Typespec() == nullptr) {
            ref_typespec* tsRef = s.MakeRef_typespec();
            tsRef->VpiParent(rhs);
            rhs->Typespec(tsRef);
            rhs->Typespec()->Actual_typespec(ts);
          }
          c->VpiSize(size);
        }
        param_assign->Rhs(rhs);
        if (rhs) {
          rhs->VpiParent(param_assign);
          if (rhs->UhdmType() == uhdmconstant) {
            constant* c = (constant*)rhs;
            param->VpiValue(c->VpiValue());
          }
        }
      }
      Param_assignment = fC->Sibling(Param_assignment);
    }
  }

  compileDesign->unlockSerializer();
  return true;
}

char flip(char c) { return (c == '0') ? '1' : '0'; }

std::string twosComplement(std::string_view bin) {
  int32_t n = bin.length();
  int32_t i;
  std::string ones, twos;
  for (i = 0; i < n; i++) ones += flip(bin[i]);
  twos = ones;
  for (i = n - 1; i >= 0; i--) {
    if (ones[i] == '1')
      twos[i] = '0';
    else {
      twos[i] = '1';
      break;
    }
  }
  if (i == -1) twos = '1' + twos;
  return twos;
}

UHDM::constant* CompileHelper::adjustSize(const UHDM::typespec* ts,
                                          DesignComponent* component,
                                          CompileDesign* compileDesign,
                                          ValuedComponentI* instance,
                                          UHDM::constant* c, bool uniquify,
                                          bool sizeMode) {
  UHDM::Serializer& s = compileDesign->getSerializer();
  UHDM::constant* result = c;
  if (ts == nullptr) {
    return result;
  }
  FileSystem* const fileSystem = FileSystem::getInstance();
  int32_t orig_size = c->VpiSize();

  bool invalidValue = false;
  int32_t sizetmp =
      Bits(ts, invalidValue, component, compileDesign, Reduce::Yes, instance,
           fileSystem->toPathId(c->VpiFile(),
                                compileDesign->getCompiler()->getSymbolTable()),
           c->VpiLineNo(), sizeMode);

  int32_t size = orig_size;
  if (c->VpiConstType() != vpiDecConst) {
    if (!invalidValue) size = sizetmp;
  }
  bool signedLhs = false;
  if (ts->UhdmType() == uhdmint_typespec) {
    int_typespec* its = (int_typespec*)ts;
    signedLhs = its->VpiSigned();
  } else if (ts->UhdmType() == uhdmlogic_typespec) {
    logic_typespec* its = (logic_typespec*)ts;
    signedLhs = its->VpiSigned();
  } else if (ts->UhdmType() == uhdmbit_typespec) {
    bit_typespec* its = (bit_typespec*)ts;
    signedLhs = its->VpiSigned();
  }

  UHDM::ExprEval eval;
  int64_t val = eval.get_value(invalidValue, c);
  bool constantIsSigned = false;
  if (!invalidValue) {
    if (c->VpiConstType() == vpiUIntConst) {
      uint64_t mask = NumUtils::getMask(size);
      uint64_t uval = (uint64_t)val;
      uval = uval & mask;
      if (uniquify) {
        UHDM::ElaboratorContext elaboratorContext(&s, false, true);
        c = (UHDM::constant*)UHDM::clone_tree(c, &elaboratorContext);
        result = c;
      }
      c->VpiValue("UINT:" + std::to_string(uval));
      c->VpiDecompile(std::to_string(uval));
      c->VpiConstType(vpiUIntConst);
      c->VpiSize(size);
    } else if (c->VpiConstType() == vpiBinaryConst) {
      if (const ref_typespec* tstmp_rt = c->Typespec()) {
        if (const typespec* tstmp = tstmp_rt->Actual_typespec()) {
          if (tstmp->UhdmType() == uhdmint_typespec) {
            int_typespec* itps = (int_typespec*)tstmp;
            if (itps->VpiSigned()) {
              constantIsSigned = true;
            }
            if (!signedLhs) {
              itps->VpiSigned(false);
            }
          }
          ts = tstmp;
        }
      }
      if (ts) {
        UHDM_OBJECT_TYPE ttype = ts->UhdmType();
        if (ttype == uhdmlogic_typespec) {
          std::string_view v = c->VpiValue();
          v.remove_prefix(4);
          if (orig_size > size) {
            if (v.size() > ((uint32_t)(orig_size - size)))
              v.remove_prefix(orig_size - size);
            c->VpiValue("BIN:" + std::string(v));
            c->VpiDecompile(v);
            c->VpiConstType(vpiBinaryConst);
            c->VpiSize(size);
          }
        } else if (ttype == uhdmint_typespec) {
          if (constantIsSigned) {
            uint64_t msb = val & 1 << (orig_size - 1);
            if (msb) {
              // 2's complement
              std::string v = std::string(c->VpiValue());
              v.erase(0, 4);
              if (signedLhs) {
                const std::string res = twosComplement(v);
                // Convert to int32_t
                val = std::strtoll(res.c_str(), nullptr, 2);
                val = -val;
              } else {
                if (size > orig_size) {
                  for (uint32_t i = 0; i < uint32_t(size - orig_size); i++) {
                    v += '1';
                  }
                  orig_size = size;
                }
                val = std::strtoll(v.c_str(), nullptr, 2);
              }
              if (uniquify) {
                UHDM::ElaboratorContext elaboratorContext(&s, false, true);
                c = (UHDM::constant*)UHDM::clone_tree(c, &elaboratorContext);
                result = c;
              }
              c->VpiValue("INT:" + std::to_string(val));
              c->VpiDecompile(std::to_string(val));
              c->VpiConstType(vpiIntConst);
            } else if ((orig_size == 1) && (val == 1)) {
              uint64_t mask = NumUtils::getMask(size);
              if (uniquify) {
                UHDM::ElaboratorContext elaboratorContext(&s, false, true);
                c = (UHDM::constant*)UHDM::clone_tree(c, &elaboratorContext);
                result = c;
              }
              c->VpiValue("UINT:" + std::to_string(mask));
              c->VpiDecompile(std::to_string(mask));
              c->VpiConstType(vpiUIntConst);
            }
          } else {
            if ((orig_size == -1) && (val == 1)) {
              uint64_t mask = NumUtils::getMask(size);
              if (uniquify) {
                UHDM::ElaboratorContext elaboratorContext(&s, false, true);
                c = (UHDM::constant*)UHDM::clone_tree(c, &elaboratorContext);
                result = c;
              }
              c->VpiValue("UINT:" + std::to_string(mask));
              c->VpiDecompile(std::to_string(mask));
              c->VpiConstType(vpiUIntConst);
            }
          }
          c->VpiSize((orig_size < size) ? orig_size : size);
        }
      }
      if (orig_size == -1) {
        // '1, '0
        uint64_t uval = (uint64_t)val;
        if (uval == 1) {
          if (uniquify) {
            UHDM::ElaboratorContext elaboratorContext(&s, false, true);
            c = (UHDM::constant*)UHDM::clone_tree(c, &elaboratorContext);
            result = c;
          }
          if (size <= 64) {
            uint64_t mask = NumUtils::getMask(size);
            uval = mask;
            c->VpiValue("UINT:" + std::to_string(uval));
            c->VpiDecompile(std::to_string(uval));
            c->VpiConstType(vpiUIntConst);
          } else {
            std::string mask(size, '1');
            c->VpiValue("BIN:" + mask);
            c->VpiDecompile(mask);
            c->VpiConstType(vpiBinaryConst);
          }
        }
        c->VpiSize(size);
      }
    } else {
      c->VpiSize(size);
    }
  }

  return result;
}

UHDM::any* CompileHelper::compileTfCall(DesignComponent* component,
                                        const FileContent* fC,
                                        NodeId Tf_call_stmt,
                                        CompileDesign* compileDesign,
                                        any* pexpr) {
  UHDM::Serializer& s = compileDesign->getSerializer();

  NodeId dollar_or_string = fC->Child(Tf_call_stmt);
  VObjectType leaf_type = fC->Type(dollar_or_string);
  NodeId tfNameNode;
  UHDM::tf_call* call = nullptr;
  std::string name;
  if (leaf_type == VObjectType::paDollar_keyword) {
    // System call, AST is:
    // n<> u<28> t<Subroutine_call> p<29> c<17> l<3>
    //     n<> u<17> t<Dollar_keyword> p<28> s<18> l<3>
    //     n<display> u<18> t<StringConst> p<28> s<27> l<3>
    //     n<> u<27> t<List_of_arguments> p<28> c<22> l<3>

    tfNameNode = fC->Sibling(dollar_or_string);
    call = s.MakeSys_func_call();
    name.assign("$").append(fC->SymName(tfNameNode));
  } else if (leaf_type == VObjectType::paImplicit_class_handle) {
    return compileComplexFuncCall(component, fC, fC->Child(Tf_call_stmt),
                                  compileDesign, Reduce::No, pexpr, nullptr,
                                  false);
  } else if (leaf_type == VObjectType::paDollar_root_keyword) {
    NodeId Dollar_root_keyword = dollar_or_string;
    NodeId nameId = fC->Sibling(Dollar_root_keyword);
    name.assign("$root.").append(fC->SymName(nameId));
    nameId = fC->Sibling(nameId);
    tfNameNode = nameId;
    func_call* fcall = s.MakeFunc_call();
    while (nameId) {
      if (fC->Type(nameId) == VObjectType::slStringConst) {
        name.append(".").append(fC->SymName(nameId));
        tfNameNode = nameId;
      } else if (fC->Type(nameId) == VObjectType::paConstant_bit_select) {
        NodeId Constant_expresion = fC->Child(nameId);
        if (Constant_expresion) {
          if (expr* select =
                  (expr*)compileExpression(component, fC, Constant_expresion,
                                           compileDesign, Reduce::No, fcall)) {
            name.append("[").append(decompileHelper(select)).append("]");
          }
          tfNameNode = nameId;
        }
      } else {
        break;
      }
      nameId = fC->Sibling(nameId);
    }
    fcall->VpiName(name);
    fcall->VpiParent(pexpr);
    call = fcall;
  } else if (leaf_type == VObjectType::paSystem_task_names) {
    tfNameNode = dollar_or_string;
    call = s.MakeSys_func_call();
    name = fC->SymName(fC->Child(dollar_or_string));
  } else if (leaf_type == VObjectType::paImplicit_class_handle) {
    NodeId handle = fC->Child(dollar_or_string);
    if (fC->Type(handle) == VObjectType::paSuper_keyword ||
        fC->Type(handle) == VObjectType::paThis_keyword ||
        fC->Type(handle) == VObjectType::paThis_dot_super) {
      return (tf_call*)compileComplexFuncCall(
          component, fC, fC->Child(Tf_call_stmt), compileDesign, Reduce::No,
          pexpr, nullptr, false);
    } else if (fC->Type(handle) == VObjectType::paDollar_root_keyword) {
      name = "$root.";
      tfNameNode = fC->Sibling(dollar_or_string);
      call = s.MakeSys_func_call();
      name += fC->SymName(tfNameNode);
    }
  } else if (leaf_type == VObjectType::paClass_scope) {
    return (tf_call*)compileComplexFuncCall(
        component, fC, fC->Child(Tf_call_stmt), compileDesign, Reduce::No,
        pexpr, nullptr, false);
  } else {
    // User call, AST is:
    // n<> u<27> t<Subroutine_call> p<28> c<17> l<3>
    //     n<show> u<17> t<StringConst> p<27> s<26> l<3>
    //     n<> u<26> t<List_of_arguments> p<27> c<21> l<3>

    tfNameNode = dollar_or_string;
    name = fC->SymName(tfNameNode);
    NodeId Constant_bit_select = fC->Sibling(tfNameNode);
    while (fC->Type(Constant_bit_select) == VObjectType::paAttribute_instance) {
      Constant_bit_select = fC->Sibling(Constant_bit_select);
    }
    if (fC->Type(Constant_bit_select) == VObjectType::paConstant_bit_select) {
      tfNameNode = fC->Sibling(Constant_bit_select);
      method_func_call* fcall = s.MakeMethod_func_call();
      const std::string_view mname = fC->SymName(tfNameNode);
      fC->populateCoreMembers(tfNameNode, tfNameNode, fcall);
      fcall->VpiName(mname);
      fcall->VpiParent(pexpr);
      ref_obj* prefix = s.MakeRef_obj();
      prefix->VpiName(name);
      prefix->VpiParent(fcall);
      fC->populateCoreMembers(dollar_or_string, dollar_or_string, prefix);
      fcall->Prefix(prefix);
      call = fcall;
    }
    std::pair<task_func*, DesignComponent*> ret =
        getTaskFunc(name, component, compileDesign, nullptr, nullptr);
    task_func* tf = ret.first;
    if (tf) {
      if (tf->UhdmType() == uhdmfunction) {
        func_call* fcall = s.MakeFunc_call();
        fcall->Function(any_cast<function*>(tf));
        call = fcall;
      } else {
        task_call* tcall = s.MakeTask_call();
        tcall->Task(any_cast<task*>(tf));
        call = tcall;
      }
      call->VpiParent(pexpr);
    }
    if (call == nullptr) {
      if (LetStmt* stmt = component->getLetStmt(name)) {
        if (compileDesign->getCompiler()
                ->getCommandLineParser()
                ->getLetExprSubstitution()) {
          // Inline the let declaration
          NodeId argListNode = fC->Sibling(tfNameNode);
          VectorOfany* arguments =
              compileTfCallArguments(component, fC, argListNode, compileDesign,
                                     Reduce::No, call, nullptr, false);
          module_inst* modTmp = s.MakeModule_inst();
          modTmp->VpiName("tmp");
          const VectorOfseq_formal_decl* decls = stmt->Ios();
          VectorOfparam_assign* passigns = s.MakeParam_assignVec();
          for (uint32_t i = 0; i < decls->size(); i++) {
            seq_formal_decl* decl = decls->at(i);
            any* actual = nullptr;
            if (i < arguments->size()) actual = arguments->at(i);
            parameter* p = s.MakeParameter();
            p->VpiName(decl->VpiName());
            param_assign* pass = s.MakeParam_assign();
            pass->Lhs(p);
            if (actual) {
              if (actual->UhdmType() == uhdmref_obj)
                component->needLateBinding((ref_obj*)actual);
              pass->Rhs(actual);
            }
            passigns->push_back(pass);
          }
          modTmp->Param_assigns(passigns);
          cont_assign* cts = s.MakeCont_assign();
          VectorOfcont_assign* assigns = s.MakeCont_assignVec();
          const expr* exp = stmt->Expr();
          cts->Rhs((expr*)exp);
          assigns->push_back(cts);
          modTmp->Cont_assigns(assigns);

          if (ElaboratorContext* elaboratorContext =
                  new ElaboratorContext(&s, false)) {
            vpiHandle defModule = NewVpiHandle(modTmp);
            elaboratorContext->m_elaborator.listenModule_inst(defModule);
            vpi_free_object(defModule);
            delete elaboratorContext;
          }
          return (any*)cts->Rhs();
        } else {
          let_expr* let = s.MakeLet_expr();
          let->Let_decl((let_decl*)stmt->Decl());
          const_cast<let_decl*>(stmt->Decl())->VpiParent(let);
          NodeId argListNode = fC->Sibling(tfNameNode);
          if (VectorOfany* arguments = compileTfCallArguments(
                  component, fC, argListNode, compileDesign, Reduce::No, let,
                  nullptr, false)) {
            VectorOfexpr* exprs = s.MakeExprVec();
            let->Arguments(exprs);
            for (auto ex : *arguments) {
              exprs->push_back((expr*)ex);
            }
          }
          return let;
        }
      }
    }

    if (call == nullptr) {
      call = s.MakeFunc_call();
      call->VpiParent(pexpr);
    }
  }
  if (call->VpiName().empty()) call->VpiName(name);
  if (call->VpiLineNo() == 0) {
    fC->populateCoreMembers(Tf_call_stmt, Tf_call_stmt, call);
  }
  NodeId argListNode = fC->Sibling(tfNameNode);
  while (fC->Type(argListNode) == VObjectType::paAttribute_instance) {
    argListNode = fC->Sibling(argListNode);
  }

  if (VectorOfany* arguments =
          compileTfCallArguments(component, fC, argListNode, compileDesign,
                                 Reduce::No, call, nullptr, false)) {
    call->Tf_call_args(arguments);
  }

  return call;
}

VectorOfany* CompileHelper::compileTfCallArguments(
    DesignComponent* component, const FileContent* fC, NodeId Arg_list_node,
    CompileDesign* compileDesign, Reduce reduce, UHDM::any* call,
    ValuedComponentI* instance, bool muteErrors) {
  FileSystem* const fileSystem = FileSystem::getInstance();
  UHDM::Serializer& s = compileDesign->getSerializer();
  if (fC->Type(Arg_list_node) == VObjectType::paSelect) {
    // Task or func call with no argument, not even ()
    return nullptr;
  }
  NodeId argumentNode = fC->Child(Arg_list_node);
  if (!argumentNode) return nullptr;
  VectorOfio_decl* io_decls = nullptr;
  if (const func_call* tf = any_cast<func_call*>(call)) {
    const function* func = tf->Function();
    if (func) io_decls = func->Io_decls();
  } else if (const task_call* tf = any_cast<task_call*>(call)) {
    const task* task = tf->Task();
    if (task) io_decls = task->Io_decls();
  }
  VectorOfany* arguments = s.MakeAnyVec();
  std::map<std::string, any*, std::less<>> args;
  std::vector<any*> argOrder;
  while (argumentNode) {
    NodeId argument = argumentNode;
    if (fC->Type(argument) == VObjectType::paArgument) {
      argument = fC->Child(argument);
    }
    NodeId sibling = fC->Sibling(argument);
    NodeId Expression;
    if ((fC->Type(argument) == VObjectType::slStringConst) &&
        (fC->Type(sibling) == VObjectType::paExpression)) {
      // arg by name
      Expression = sibling;
      UHDM::any* exp =
          compileExpression(component, fC, Expression, compileDesign, reduce,
                            call, instance, muteErrors);
      if (exp) {
        if (exp->VpiParent() == nullptr) exp->VpiParent(call);
        args.emplace(fC->SymName(argument), exp);
        argOrder.push_back(exp);
      }
      argumentNode = fC->Sibling(argumentNode);
    } else if (((fC->Type(argument) == VObjectType::paUnary_Tilda) ||
                (fC->Type(argument) == VObjectType::paUnary_Not)) &&
               (fC->Type(sibling) == VObjectType::paExpression)) {
      // arg by position
      Expression = argument;
      UHDM::any* exp =
          compileExpression(component, fC, Expression, compileDesign, reduce,
                            call, instance, muteErrors);
      if (exp) {
        if (exp->VpiParent() == nullptr) exp->VpiParent(call);
        arguments->push_back(exp);
      }
      argumentNode = fC->Sibling(argumentNode);
    } else {
      // arg by position
      Expression = argument;
      if (Expression) {
        UHDM::any* exp =
            compileExpression(component, fC, Expression, compileDesign, reduce,
                              call, instance, muteErrors);
        if (exp) {
          arguments->push_back(exp);
          if (exp->VpiParent() == nullptr) exp->VpiParent(call);
        }
      } else {
        constant* c = s.MakeConstant();
        c->VpiValue("INT:0");
        c->VpiDecompile("0");
        c->VpiSize(64);
        c->VpiConstType(vpiIntConst);
        fC->populateCoreMembers(argumentNode, argumentNode, c);
        arguments->push_back(c);
      }
    }
    argumentNode = fC->Sibling(argumentNode);
  }
  if (NodeId clocking = fC->Sibling(Arg_list_node)) {
    if (fC->Type(clocking) == VObjectType::paClocking_event) {
      UHDM::any* exp = compileExpression(component, fC, clocking, compileDesign,
                                         reduce, call, instance, muteErrors);
      if (exp) {
        arguments->push_back(exp);
        if (exp->VpiParent() == nullptr) exp->VpiParent(call);
      }
    }
  }
  if (!args.empty()) {
    if (io_decls) {
      for (io_decl* decl : *io_decls) {
        const std::string_view name = decl->VpiName();
        std::map<std::string, any*>::iterator itr = args.find(name);
        if (itr != args.end()) {
          arguments->push_back((*itr).second);
        } else {
          constant* c = s.MakeConstant();
          c->VpiFile(fileSystem->toPath(fC->getFileId()));
          c->VpiValue("INT:0");
          c->VpiDecompile("0");
          c->VpiSize(64);
          c->VpiConstType(vpiIntConst);
          arguments->push_back(c);
        }
      }
    } else {
      for (any* exp : argOrder) {
        arguments->push_back(exp);
      }
    }
  }

  return arguments;
}

UHDM::assignment* CompileHelper::compileBlockingAssignment(
    DesignComponent* component, const FileContent* fC,
    NodeId Operator_assignment, bool blocking, CompileDesign* compileDesign,
    UHDM::any* pstmt, ValuedComponentI* instance) {
  UHDM::Serializer& s = compileDesign->getSerializer();
  NodeId Variable_lvalue;
  if (fC->Type(Operator_assignment) == VObjectType::paVariable_lvalue) {
    Variable_lvalue = Operator_assignment;
  } else if (fC->Type(Operator_assignment) == VObjectType::slStringConst) {
    Variable_lvalue = Operator_assignment;
  } else {
    Variable_lvalue = fC->Child(Operator_assignment);
  }
  assignment* assign = s.MakeAssignment();
  UHDM::expr* lhs_rf = nullptr;
  UHDM::any* rhs_rf = nullptr;
  NodeId Delay_or_event_control;
  NodeId AssignOp_Assign;
  if (fC->Type(Variable_lvalue) == VObjectType::paHierarchical_identifier ||
      fC->Type(Variable_lvalue) == VObjectType::slStringConst) {
    NodeId Variable_lvalue = Operator_assignment;
    Delay_or_event_control = fC->Sibling(Variable_lvalue);
    NodeId Expression = fC->Sibling(Delay_or_event_control);
    lhs_rf = any_cast<expr*>(compileExpression(component, fC, Variable_lvalue,
                                               compileDesign, Reduce::No,
                                               assign, instance));
    AssignOp_Assign = InvalidNodeId;
    if (fC->Type(Delay_or_event_control) == VObjectType::paDynamic_array_new) {
      method_func_call* fcall = s.MakeMethod_func_call();
      fC->populateCoreMembers(Delay_or_event_control, Delay_or_event_control,
                              fcall);
      fcall->VpiName("new");
      NodeId List_of_arguments = fC->Child(Delay_or_event_control);
      if (List_of_arguments) {
        if (VectorOfany* arguments = compileTfCallArguments(
                component, fC, Delay_or_event_control, compileDesign,
                Reduce::No, fcall, nullptr, false)) {
          fcall->Tf_call_args(arguments);
        }
      }
      Delay_or_event_control = InvalidNodeId;
      rhs_rf = fcall;
    } else {
      rhs_rf = compileExpression(component, fC, Expression, compileDesign,
                                 Reduce::No, assign, instance);
    }
  } else if (fC->Type(Variable_lvalue) == VObjectType::paVariable_lvalue) {
    AssignOp_Assign = fC->Sibling(Variable_lvalue);
    NodeId Hierarchical_identifier = fC->Child(Variable_lvalue);
    if (fC->Type(fC->Child(Hierarchical_identifier)) ==
        VObjectType::paHierarchical_identifier) {
      Hierarchical_identifier = fC->Child(Hierarchical_identifier);
      Hierarchical_identifier = fC->Child(Hierarchical_identifier);
    } else if (fC->Type(Hierarchical_identifier) !=
               VObjectType::paPs_or_hierarchical_identifier) {
      Hierarchical_identifier = Variable_lvalue;
    }

    lhs_rf = any_cast<expr*>(
        compileExpression(component, fC, Hierarchical_identifier, compileDesign,
                          Reduce::No, assign, instance));
    NodeId Expression;
    if (fC->Type(AssignOp_Assign) == VObjectType::paExpression) {
      Expression = AssignOp_Assign;
      AssignOp_Assign = InvalidNodeId;
    } else if (fC->Type(AssignOp_Assign) ==
               VObjectType::paDelay_or_event_control) {
      Delay_or_event_control = AssignOp_Assign;
      Expression = fC->Sibling(AssignOp_Assign);
      AssignOp_Assign = InvalidNodeId;
    } else {
      Expression = fC->Sibling(AssignOp_Assign);
    }
    rhs_rf = compileExpression(component, fC, Expression, compileDesign,
                               Reduce::No, assign, instance);
  } else if (fC->Type(Operator_assignment) ==
             VObjectType::paHierarchical_identifier) {
    //  = new ...
    NodeId Hierarchical_identifier = Operator_assignment;
    NodeId Select = fC->Sibling(Hierarchical_identifier);
    NodeId Class_new = fC->Sibling(Select);
    NodeId List_of_arguments = fC->Child(Class_new);
    lhs_rf = any_cast<expr*>(
        compileExpression(component, fC, Hierarchical_identifier, compileDesign,
                          Reduce::No, assign, instance));
    method_func_call* fcall = s.MakeMethod_func_call();
    fcall->VpiName("new");
    fcall->VpiParent(assign);
    fC->populateCoreMembers(Hierarchical_identifier, Hierarchical_identifier,
                            fcall);
    if (List_of_arguments) {
      if (VectorOfany* arguments = compileTfCallArguments(
              component, fC, List_of_arguments, compileDesign, Reduce::No,
              fcall, nullptr, false)) {
        fcall->Tf_call_args(arguments);
      }
    }

    rhs_rf = fcall;
  }

  if (Delay_or_event_control &&
      (fC->Type(Delay_or_event_control) != VObjectType::paSelect)) {
    UHDM::delay_control* delay_control = s.MakeDelay_control();
    assign->Delay_control(delay_control);
    delay_control->VpiParent(assign);
    NodeId Delay_control = fC->Child(Delay_or_event_control);
    NodeId IntConst = fC->Child(Delay_control);
    const std::string_view value = fC->SymName(IntConst);
    delay_control->VpiDelay(value);
    fC->populateCoreMembers(fC->Child(Delay_control), fC->Child(Delay_control),
                            delay_control);
  }
  if (AssignOp_Assign)
    assign->VpiOpType(UhdmWriter::getVpiOpType(fC->Type(AssignOp_Assign)));
  else
    assign->VpiOpType(vpiAssignmentOp);
  if (blocking) assign->VpiBlocking(true);
  assign->Lhs(lhs_rf);
  assign->Rhs(rhs_rf);
  return assign;
}

void CompileHelper::setParentNoOverride(any* obj, any* parent) {
  if (obj) {
    if (!obj->VpiParent()) {
      obj->VpiParent(parent);
    } else if (obj->VpiParent()->UhdmType() == uhdmref_obj) {
      const_cast<any*>(obj->VpiParent())->VpiParent(parent);
    }
  }
}

UHDM::array_var* CompileHelper::compileArrayVar(DesignComponent* component,
                                                const FileContent* fC,
                                                NodeId varId,
                                                CompileDesign* compileDesign,
                                                UHDM::any* pexpr,
                                                ValuedComponentI* instance) {
  UHDM::Serializer& s = compileDesign->getSerializer();
  array_var* result = s.MakeArray_var();

  return result;
}

std::vector<UHDM::attribute*>* CompileHelper::compileAttributes(
    DesignComponent* component, const FileContent* fC, NodeId nodeId,
    CompileDesign* compileDesign, UHDM::any* pexpr) {
  UHDM::Serializer& s = compileDesign->getSerializer();
  std::vector<UHDM::attribute*>* results = nullptr;
  if (fC->Type(nodeId) == VObjectType::paAttribute_instance) {
    results = s.MakeAttributeVec();
    while (fC->Type(nodeId) == VObjectType::paAttribute_instance) {
      NodeId Attr_spec = fC->Child(nodeId);
      while (fC->Type(Attr_spec) == VObjectType::paAttr_spec) {
        UHDM::attribute* attribute = s.MakeAttribute();
        NodeId Attr_name = fC->Child(Attr_spec);
        const std::string_view name = fC->SymName(fC->Child(Attr_name));
        attribute->VpiName(name);
        attribute->VpiParent(pexpr);
        fC->populateCoreMembers(Attr_spec, Attr_spec, attribute);
        results->push_back(attribute);
        if (NodeId Constant_expression = fC->Sibling(Attr_name)) {
          if (UHDM::expr* expr = (UHDM::expr*)compileExpression(
                  component, fC, Constant_expression, compileDesign, Reduce::No,
                  attribute)) {
            attribute->VpiValue(expr->VpiValue());
          }
        }
        Attr_spec = fC->Sibling(Attr_spec);
      }
      nodeId = fC->Sibling(nodeId);
    }
  }
  return results;
}

UHDM::clocking_block* CompileHelper::compileClockingBlock(
    DesignComponent* component, const FileContent* fC, NodeId nodeId,
    CompileDesign* compileDesign, UHDM::any* pstmt,
    ValuedComponentI* instance) {
  UHDM::Serializer& s = compileDesign->getSerializer();
  UHDM::clocking_block* cblock = s.MakeClocking_block();

  NodeId clocking_block_type = fC->Child(nodeId);
  NodeId clocking_block_name;
  std::string name;
  if (fC->Type(clocking_block_type) == VObjectType::paDEFAULT) {
  } else if (fC->Type(clocking_block_type) == VObjectType::paGLOBAL) {
  } else if (fC->Type(clocking_block_type) == VObjectType::slStringConst) {
    clocking_block_name = clocking_block_type;
  }
  NodeId clocking_event = fC->Sibling(clocking_block_type);
  if (fC->Type(clocking_event) == VObjectType::slStringConst) {
    clocking_block_name = clocking_event;
    clocking_event = fC->Sibling(clocking_block_name);
  }
  if (clocking_block_name)
    name = fC->SymName(clocking_block_name);
  else
    name = "unnamed_clocking_block";
  cblock->VpiName(name);
  fC->populateCoreMembers(nodeId, nodeId, cblock);
  event_control* ctrl = compileClocking_event(component, fC, clocking_event,
                                              compileDesign, cblock, instance);
  cblock->Clocking_event(ctrl);
  NodeId clocking_item = fC->Sibling(clocking_event);
  while (clocking_item) {
    if (fC->Type(clocking_item) == VObjectType::paClocking_item) {
      NodeId item = fC->Child(clocking_item);
      VObjectType direction = fC->Type(item);
      UHDM::delay_control* dcInp = nullptr;
      UHDM::delay_control* dcOut = nullptr;
      int32_t inputEdge = 0;
      int32_t outputEdge = 0;
      if (direction == VObjectType::paDefaultSkew_IntputOutput) {
        NodeId Clocking_skew = fC->Child(item);
        if (Clocking_skew) {
          NodeId Edge = fC->Child(Clocking_skew);
          NodeId Skew = Clocking_skew;
          if (fC->Type(Edge) == VObjectType::paEdge_Negedge) {
            cblock->VpiInputEdge(vpiNegedge);
            Skew = fC->Sibling(Edge);
          } else if (fC->Type(Edge) == VObjectType::paEdge_Posedge) {
            cblock->VpiInputEdge(vpiPosedge);
            Skew = fC->Sibling(Edge);
          } else if (fC->Type(Edge) == VObjectType::paEdge_Edge) {
            cblock->VpiInputEdge(vpiAnyEdge);
            Skew = fC->Sibling(Edge);
          }
          if (Skew) {
            UHDM::delay_control* dc = (delay_control*)compileDelayControl(
                component, fC, Skew, compileDesign, cblock, instance);
            cblock->Input_skew(dc);
          }
          Clocking_skew = fC->Sibling(Clocking_skew);
          if (Clocking_skew) {
            NodeId Edge = fC->Child(Clocking_skew);
            NodeId Skew = Clocking_skew;
            if (fC->Type(Edge) == VObjectType::paEdge_Negedge) {
              cblock->VpiOutputEdge(vpiNegedge);
              Skew = fC->Sibling(Edge);
            } else if (fC->Type(Edge) == VObjectType::paEdge_Posedge) {
              cblock->VpiOutputEdge(vpiPosedge);
              Skew = fC->Sibling(Edge);
            } else if (fC->Type(Edge) == VObjectType::paEdge_Edge) {
              cblock->VpiOutputEdge(vpiAnyEdge);
              Skew = fC->Sibling(Edge);
            }
            if (Skew) {
              UHDM::delay_control* dc = (delay_control*)compileDelayControl(
                  component, fC, Clocking_skew, compileDesign, cblock,
                  instance);
              cblock->Output_skew(dc);
            }
          }
        }
      }
      if (direction == VObjectType::paDefaultSkew_Intput) {
        NodeId Clocking_skew = fC->Child(item);
        if (Clocking_skew) {
          NodeId Edge = fC->Child(Clocking_skew);
          NodeId Skew = Clocking_skew;
          if (fC->Type(Edge) == VObjectType::paEdge_Negedge) {
            cblock->VpiInputEdge(vpiNegedge);
            Skew = fC->Sibling(Edge);
          } else if (fC->Type(Edge) == VObjectType::paEdge_Posedge) {
            cblock->VpiInputEdge(vpiPosedge);
            Skew = fC->Sibling(Edge);
          } else if (fC->Type(Edge) == VObjectType::paEdge_Edge) {
            cblock->VpiInputEdge(vpiAnyEdge);
            Skew = fC->Sibling(Edge);
          }
          if (Skew) {
            UHDM::delay_control* dc = (delay_control*)compileDelayControl(
                component, fC, Skew, compileDesign, cblock, instance);
            cblock->Input_skew(dc);
          }
        }
      }
      if (direction == VObjectType::paDefaultSkew_Output) {
        NodeId Clocking_skew = fC->Child(item);
        if (Clocking_skew) {
          NodeId Edge = fC->Child(Clocking_skew);
          NodeId Skew = Clocking_skew;
          if (fC->Type(Edge) == VObjectType::paEdge_Negedge) {
            cblock->VpiOutputEdge(vpiNegedge);
            Skew = fC->Sibling(Edge);
          } else if (fC->Type(Edge) == VObjectType::paEdge_Posedge) {
            cblock->VpiOutputEdge(vpiPosedge);
            Skew = fC->Sibling(Edge);
          } else if (fC->Type(Edge) == VObjectType::paEdge_Edge) {
            cblock->VpiOutputEdge(vpiAnyEdge);
            Skew = fC->Sibling(Edge);
          }
          if (Skew) {
            UHDM::delay_control* dc = (delay_control*)compileDelayControl(
                component, fC, Skew, compileDesign, cblock, instance);
            cblock->Output_skew(dc);
          }
        }
      } else if (direction == VObjectType::paClockingDir_Input) {
        NodeId Clocking_skew = fC->Child(item);
        if (Clocking_skew) {
          NodeId Edge = fC->Child(Clocking_skew);
          NodeId Skew = Clocking_skew;
          if (fC->Type(Edge) == VObjectType::paEdge_Negedge) {
            inputEdge = vpiNegedge;
            Skew = fC->Sibling(Edge);
          } else if (fC->Type(Edge) == VObjectType::paEdge_Posedge) {
            inputEdge = vpiPosedge;
            Skew = fC->Sibling(Edge);
          } else if (fC->Type(Edge) == VObjectType::paEdge_Edge) {
            inputEdge = vpiAnyEdge;
            Skew = fC->Sibling(Edge);
          }
          if (Skew) {
            dcInp = (delay_control*)compileDelayControl(
                component, fC, Skew, compileDesign, cblock, instance);
          }
        }
      } else if (direction == VObjectType::paClockingDir_Output) {
        NodeId Clocking_skew = fC->Child(item);
        if (Clocking_skew) {
          NodeId Edge = fC->Child(Clocking_skew);
          NodeId Skew = Clocking_skew;
          if (fC->Type(Edge) == VObjectType::paEdge_Negedge) {
            outputEdge = vpiNegedge;
            Skew = fC->Sibling(Edge);
          } else if (fC->Type(Edge) == VObjectType::paEdge_Posedge) {
            outputEdge = vpiPosedge;
            Skew = fC->Sibling(Edge);
          } else if (fC->Type(Edge) == VObjectType::paEdge_Edge) {
            outputEdge = vpiAnyEdge;
            Skew = fC->Sibling(Edge);
          }
          if (Skew) {
            dcOut = (delay_control*)compileDelayControl(
                component, fC, Skew, compileDesign, cblock, instance);
          }
        }
      } else if (direction == VObjectType::paClockingDir_InputOutput) {
        NodeId Clocking_skew = fC->Child(item);
        if (Clocking_skew) {
          NodeId Edge = fC->Child(Clocking_skew);
          NodeId Skew = Clocking_skew;
          if (fC->Type(Edge) == VObjectType::paEdge_Negedge) {
            inputEdge = vpiNegedge;
            Skew = fC->Sibling(Edge);
          } else if (fC->Type(Edge) == VObjectType::paEdge_Posedge) {
            inputEdge = vpiPosedge;
            Skew = fC->Sibling(Edge);
          } else if (fC->Type(Edge) == VObjectType::paEdge_Edge) {
            inputEdge = vpiAnyEdge;
            Skew = fC->Sibling(Edge);
          }
          if (Skew) {
            dcInp = (delay_control*)compileDelayControl(
                component, fC, Skew, compileDesign, cblock, instance);
          }

          Clocking_skew = fC->Sibling(Clocking_skew);
          if (Clocking_skew) {
            NodeId Edge = fC->Child(Clocking_skew);
            NodeId Skew = Clocking_skew;
            if (fC->Type(Edge) == VObjectType::paEdge_Negedge) {
              outputEdge = vpiNegedge;
              Skew = fC->Sibling(Edge);
            } else if (fC->Type(Edge) == VObjectType::paEdge_Posedge) {
              outputEdge = vpiPosedge;
              Skew = fC->Sibling(Edge);
            } else if (fC->Type(Edge) == VObjectType::paEdge_Edge) {
              outputEdge = vpiAnyEdge;
              Skew = fC->Sibling(Edge);
            }
            if (Skew) {
              dcOut = (delay_control*)compileDelayControl(
                  component, fC, Skew, compileDesign, cblock, instance);
            }
          }
        }
      } else if (direction == VObjectType::paClockingDir_Inout) {
        // No skew value
      }

      NodeId List_of_clocking_decl_assign = fC->Sibling(item);
      if (List_of_clocking_decl_assign) {
        NodeId Clocking_decl_assign = fC->Child(List_of_clocking_decl_assign);
        VectorOfclocking_io_decl* ios = cblock->Clocking_io_decls();
        if (ios == nullptr) {
          cblock->Clocking_io_decls(s.MakeClocking_io_declVec());
          ios = cblock->Clocking_io_decls();
        }

        while (Clocking_decl_assign) {
          NodeId Identifier = fC->Child(Clocking_decl_assign);
          NodeId Expr = fC->Sibling(Identifier);
          UHDM::clocking_io_decl* io = s.MakeClocking_io_decl();
          io->VpiInputEdge(inputEdge);
          io->VpiOutputEdge(outputEdge);
          io->VpiParent(cblock);
          fC->populateCoreMembers(Clocking_decl_assign, Clocking_decl_assign,
                                  io);
          if (Expr) {
            if (UHDM::expr* exp =
                    (expr*)compileExpression(component, fC, Expr, compileDesign,
                                             Reduce::No, io, instance)) {
              io->Expr(exp);
            }
          }
          ios->push_back(io);
          const std::string_view sigName = fC->SymName(Identifier);
          io->VpiName(sigName);
          if (direction == VObjectType::paClockingDir_Input) {
            io->Input_skew(dcInp);
            io->VpiDirection(vpiInput);
          } else if (direction == VObjectType::paClockingDir_Output) {
            io->Output_skew(dcOut);
            io->VpiDirection(vpiOutput);
          } else if (direction == VObjectType::paClockingDir_InputOutput) {
            io->Input_skew(dcInp);
            io->Output_skew(dcOut);
            io->VpiDirection(vpiOutput);
          } else if (direction == VObjectType::paClockingDir_Inout) {
            io->VpiDirection(vpiInout);
          }
          Clocking_decl_assign = fC->Sibling(Clocking_decl_assign);
        }
      }
    }
    clocking_item = fC->Sibling(clocking_item);
  }
  return cblock;
}

UHDM::event_control* CompileHelper::compileClocking_event(
    DesignComponent* component, const FileContent* fC, NodeId nodeId,
    CompileDesign* compileDesign, UHDM::any* pexpr,
    ValuedComponentI* instance) {
  UHDM::Serializer& s = compileDesign->getSerializer();
  event_control* ctrl = s.MakeEvent_control();
  ctrl->VpiParent(pexpr);
  fC->populateCoreMembers(nodeId, nodeId, ctrl);
  NodeId identifier = fC->Child(nodeId);
  if (UHDM::any* exp =
          compileExpression(component, fC, identifier, compileDesign,
                            Reduce::No, ctrl, instance)) {
    ctrl->VpiCondition(exp);
  }
  return ctrl;
}

bool CompileHelper::isSelected(const FileContent* fC,
                               NodeId ps_or_hierarchical_identifier) {
  NodeId Constant_select = fC->Sibling(ps_or_hierarchical_identifier);
  NodeId Constant_bit_select = fC->Child(Constant_select);
  NodeId Constant_expression = fC->Child(Constant_bit_select);
  NodeId Constant_part_select_range = fC->Sibling(Constant_bit_select);
  if (Constant_part_select_range) {
    return true;
  }
  if (Constant_expression) return true;
  return false;
}

void CompileHelper::adjustUnsized(constant* c, int32_t size) {
  if (c == nullptr) return;
  int32_t csize = c->VpiSize();
  if (csize == -1) {
    UHDM::ExprEval eval;
    bool invalidValue = false;
    uint64_t lv = eval.get_uvalue(invalidValue, c);
    if (lv == 1) {
      if (size <= 64) {
        uint64_t mask = NumUtils::getMask(size);
        c->VpiValue("UINT:" + std::to_string(mask));
        c->VpiDecompile(std::to_string(mask));
        c->VpiConstType(vpiUIntConst);
      } else {
        std::string mask(size, '1');
        c->VpiValue("BIN:" + mask);
        c->VpiDecompile(mask);
        c->VpiConstType(vpiBinaryConst);
      }
    }
  }
}

int32_t CompileHelper::adjustOpSize(const typespec* tps, expr* cop,
                                    int32_t opIndex, UHDM::expr* rhs,
                                    DesignComponent* component,
                                    CompileDesign* compileDesign,
                                    ValuedComponentI* instance) {
  FileSystem* const fileSystem = FileSystem::getInstance();
  bool invalidValue = false;
  int32_t csize = cop->VpiSize();
  if (csize == 0) {
    expr* vexp = reduceExpr(
        cop, invalidValue, component, compileDesign, instance,
        fileSystem->toPathId(cop->VpiFile(),
                             compileDesign->getCompiler()->getSymbolTable()),
        cop->VpiLineNo(), nullptr);
    if (invalidValue == false && vexp) csize = vexp->VpiSize();
  }

  const typespec* rtps = nullptr;
  if (const UHDM::ref_typespec* rt = rhs->Typespec()) {
    rtps = rt->Actual_typespec();
  }
  if (rtps == nullptr) {
    rtps = tps;
  }
  if (rtps->UhdmType() == uhdmstruct_typespec) {
    struct_typespec* stps = (struct_typespec*)rtps;
    int32_t index = 0;
    for (typespec_member* member : *stps->Members()) {
      if (index == opIndex) {
        const UHDM::typespec* mtps = nullptr;
        if (const UHDM::ref_typespec* rt = member->Typespec()) {
          mtps = rt->Actual_typespec();
        }
        int32_t ncsize = Bits(
            mtps, invalidValue, component, compileDesign, Reduce::Yes, instance,
            fileSystem->toPathId(
                member->VpiFile(),
                compileDesign->getCompiler()->getSymbolTable()),
            member->VpiLineNo(), false);
        // Fix the size of the member:
        adjustUnsized(any_cast<constant*>(cop), ncsize);
        cop->VpiSize(ncsize);
        break;
      }
      index++;
    }
  } else if (rtps->UhdmType() == uhdmarray_typespec) {
    array_typespec* atps = (array_typespec*)rtps;
    if (const ref_typespec* ert = atps->Elem_typespec()) {
      int32_t ncsize = Bits(
          ert->Actual_typespec(), invalidValue, component, compileDesign,
          Reduce::Yes, instance,
          fileSystem->toPathId(rtps->VpiFile(),
                               compileDesign->getCompiler()->getSymbolTable()),
          rtps->VpiLineNo(), false);
      // Fix the size of the member:
      adjustUnsized(any_cast<constant*>(cop), ncsize);
      cop->VpiSize(ncsize);
    }
  } else if (rtps->UhdmType() == uhdmlogic_typespec) {
    uint64_t fullSize = Bits(
        rtps, invalidValue, component, compileDesign, Reduce::Yes, instance,
        fileSystem->toPathId(rtps->VpiFile(),
                             compileDesign->getCompiler()->getSymbolTable()),
        rtps->VpiLineNo(), false);
    uint64_t innerSize = Bits(
        rtps, invalidValue, component, compileDesign, Reduce::Yes, instance,
        fileSystem->toPathId(rtps->VpiFile(),
                             compileDesign->getCompiler()->getSymbolTable()),
        rtps->VpiLineNo(), true);
    int32_t ncsize = fullSize / innerSize;
    // Fix the size of the member:
    adjustUnsized(any_cast<constant*>(cop), ncsize);
    cop->VpiSize(ncsize);
  } else {
    int32_t ncsize = Bits(
        rtps, invalidValue, component, compileDesign, Reduce::Yes, instance,
        fileSystem->toPathId(rtps->VpiFile(),
                             compileDesign->getCompiler()->getSymbolTable()),
        rtps->VpiLineNo(), false);
    // Fix the size of the member:
    adjustUnsized(any_cast<constant*>(cop), ncsize);
    cop->VpiSize(ncsize);
  }

  return cop->VpiSize();
}

UHDM::expr* CompileHelper::expandPatternAssignment(const typespec* tps,
                                                   UHDM::expr* rhs,
                                                   DesignComponent* component,
                                                   CompileDesign* compileDesign,
                                                   ValuedComponentI* instance) {
  FileSystem* const fileSystem = FileSystem::getInstance();
  Serializer& s = compileDesign->getSerializer();

  expr* result = rhs;
  VectorOfany* vars = nullptr;
  if (tps == nullptr) return result;
  if (tps->UhdmType() == uhdmpacked_array_typespec ||
      tps->UhdmType() == uhdmlogic_typespec ||
      tps->UhdmType() == uhdmstruct_typespec) {
    vars = s.MakeAnyVec();
  }

  bool invalidValue = false;
  uint64_t size =
      Bits(tps, invalidValue, component, compileDesign, Reduce::Yes, instance,
           fileSystem->toPathId(rhs->VpiFile(),
                                compileDesign->getCompiler()->getSymbolTable()),
           rhs->VpiLineNo(), false);
  uint64_t patternSize = 0;

  UHDM::ExprEval eval(true);
  rhs = eval.flattenPatternAssignments(s, tps, rhs);

  std::vector<int32_t> values(size, 0);
  if (rhs->UhdmType() == uhdmoperation) {
    operation* op = (operation*)rhs;
    int32_t opType = op->VpiOpType();
    if (opType == vpiConditionOp) {
      VectorOfany* ops = op->Operands();
      ops->at(1) = expandPatternAssignment(tps, (expr*)ops->at(1), component,
                                           compileDesign, instance);
      ops->at(2) = expandPatternAssignment(tps, (expr*)ops->at(2), component,
                                           compileDesign, instance);
      return result;
    } else if (opType == vpiAssignmentPatternOp) {
      VectorOfany* operands = op->Operands();
      if (operands) {
        // Get default
        int32_t defaultval = 0;
        bool taggedPattern = false;
        for (any* op : *operands) {
          if (op->UhdmType() == uhdmtagged_pattern) {
            taggedPattern = true;
            tagged_pattern* tp = (tagged_pattern*)op;
            if (const UHDM::ref_typespec* rt = tp->Typespec()) {
              if (const typespec* tpsi = rt->Actual_typespec()) {
                if (tpsi->VpiName() == "default") {
                  bool invalidValue = false;
                  UHDM::ExprEval eval;
                  defaultval = eval.get_value(
                      invalidValue,
                      reduceExpr(
                          tp->Pattern(), invalidValue, component, compileDesign,
                          instance,
                          fileSystem->toPathId(
                              tp->Pattern()->VpiFile(),
                              compileDesign->getCompiler()->getSymbolTable()),
                          tp->Pattern()->VpiLineNo(), nullptr));

                  break;
                }
              }
            }
          }
        }
        if (taggedPattern) {
          const typespec* rtps = nullptr;
          if (const ref_typespec* rt = rhs->Typespec()) {
            rtps = rt->Actual_typespec();
          }
          if (rtps == nullptr) {
            rtps = tps;
          }
          if (rtps->UhdmType() == uhdmstruct_typespec) {
            struct_typespec* stps = (struct_typespec*)rtps;
            int32_t valIndex = 0;
            // Apply default
            for (typespec_member* member : *stps->Members()) {
              uint64_t csize =
                  Bits(member, invalidValue, component, compileDesign,
                       Reduce::Yes, instance,
                       fileSystem->toPathId(
                           rhs->VpiFile(),
                           compileDesign->getCompiler()->getSymbolTable()),
                       rhs->VpiLineNo(), false);
              patternSize += csize;
              if (invalidValue) {
                return result;
              }
              for (uint64_t i = 0; i < csize; i++) {
                if (valIndex > (int32_t)(size - 1)) {
                  break;
                }
                {
                  int shift = (csize - 1 - i);
                  if (shift < 0 || shift >= 64) {
                    return result;
                  }
                }
                values[valIndex] =
                    (defaultval & (1 << (csize - 1 - i))) ? 1 : 0;
                valIndex++;
              }
            }
            valIndex = 0;
            for (typespec_member* member : *stps->Members()) {
              uint64_t csize =
                  Bits(member, invalidValue, component, compileDesign,
                       Reduce::Yes, instance,
                       fileSystem->toPathId(
                           rhs->VpiFile(),
                           compileDesign->getCompiler()->getSymbolTable()),
                       rhs->VpiLineNo(), false);

              for (any* op : *operands) {
                bool found = false;
                int32_t val = 0;
                if (op->UhdmType() == uhdmtagged_pattern) {
                  taggedPattern = true;
                  tagged_pattern* tp = (tagged_pattern*)op;
                  if (const UHDM::ref_typespec* rt = tp->Typespec()) {
                    if (const typespec* tpsi = rt->Actual_typespec()) {
                      if (tpsi->VpiName() == member->VpiName()) {
                        bool invalidValue = false;
                        UHDM::ExprEval eval;
                        val = eval.get_value(
                            invalidValue,
                            reduceExpr(tp->Pattern(), invalidValue, component,
                                       compileDesign, instance,
                                       fileSystem->toPathId(
                                           tp->Pattern()->VpiFile(),
                                           compileDesign->getCompiler()
                                               ->getSymbolTable()),
                                       tp->Pattern()->VpiLineNo(), nullptr));
                        found = true;
                        if (invalidValue) {
                          return result;
                        }
                      }
                    }
                  }
                }

                for (uint64_t i = 0; i < csize; i++) {
                  if (valIndex > (int32_t)(size - 1)) {
                    break;
                  }
                  {
                    int shift = (csize - 1 - i);
                    if (shift < 0 || shift >= 64) {
                      return result;
                    }
                  }
                  if (found) {
                    values[valIndex] = (val & (1 << (csize - 1 - i))) ? 1 : 0;
                  }
                  valIndex++;
                }
              }
            }
          } else if (rtps->UhdmType() == uhdmlogic_typespec) {
            // Apply default
            // parameter logic[7:0] P = '{default: 1};
            patternSize += size;
            for (uint64_t i = 0; i < size; i++) {
              values[i] = defaultval;
            }
            // Apply any other indexed value
            for (any* op : *operands) {
              if (op->UhdmType() == uhdmtagged_pattern) {
                taggedPattern = true;
                tagged_pattern* tp = (tagged_pattern*)op;
                if (const UHDM::ref_typespec* rt = tp->Typespec()) {
                  if (const typespec* tpsi = rt->Actual_typespec()) {
                    if (tpsi->UhdmType() == uhdminteger_typespec) {
                      integer_typespec* itps = (integer_typespec*)tpsi;
                      std::string_view v = itps->VpiValue();
                      v.remove_prefix(std::string_view("INT:").length());
                      int64_t index;
                      if (NumUtils::parseInt64(v, &index)) {
                        any* pattern = tp->Pattern();
                        if (pattern->UhdmType() == uhdmconstant) {
                          constant* c = (constant*)pattern;
                          UHDM::ExprEval eval;
                          int32_t val = eval.get_value(invalidValue, c);
                          if (index >= 0 && index < ((int64_t)size))
                            values[size - index - 1] = val;
                        }
                      }
                    }
                  }
                }
              }
            }
          }
        } else {
          int32_t valIndex = 0;
          int32_t opIndex = 0;
          for (any* op : *operands) {
            expr* cop = (expr*)op;
            UHDM::ExprEval eval;
            expr* vexp = reduceExpr(
                cop, invalidValue, component, compileDesign, instance,
                fileSystem->toPathId(
                    cop->VpiFile(),
                    compileDesign->getCompiler()->getSymbolTable()),
                cop->VpiLineNo(), nullptr);
            uint64_t v = eval.get_uvalue(invalidValue, vexp);
            int32_t csize = adjustOpSize(tps, cop, opIndex, rhs, component,
                                         compileDesign, instance);
            if (invalidValue) {
              return result;
            }
            patternSize += csize;
            for (int32_t i = 0; i < csize; i++) {
              if (valIndex > (int32_t)(size - 1)) {
                break;
              }

              int shift = (csize - 1 - i);
              if (shift < 0 || shift >= 64) {
                return result;
              }

              values[valIndex] = (v & (1ULL << (shift))) ? 1 : 0;
              valIndex++;
            }
            opIndex++;
          }
        }
      }
    }
  }

  if (tps->UhdmType() == uhdmpacked_array_typespec) {
    const packed_array_typespec* atps = (const packed_array_typespec*)tps;
    const typespec* etps = nullptr;
    if (const ref_typespec* rt = atps->Elem_typespec()) {
      etps = rt->Actual_typespec();
    }
    if (etps != nullptr) {
      UHDM_OBJECT_TYPE etps_type = etps->UhdmType();
      if (size > 1) {
        if (etps_type == uhdmenum_typespec) {
          packed_array_var* array = s.MakePacked_array_var();
          array->VpiSize(size);
          array->Ranges(atps->Ranges());
          array->Elements(vars);
          for (uint32_t i = 0; i < size; i++) {
            vars->push_back(s.MakeEnum_var());
          }

          for (uint32_t i = 0; i < size; i++) {
            if (vars && ((int32_t)i < (int32_t)(vars->size()))) {
              ((variables*)(*vars)[i])
                  ->VpiValue("UINT:" + std::to_string(values[i]));
            }
          }

          result = array;
        }
      }
    }
  } else if (tps->UhdmType() == uhdmlogic_typespec) {
    if (patternSize) {
      constant* c = s.MakeConstant();
      c->VpiFile(rhs->VpiFile());
      c->VpiLineNo(rhs->VpiLineNo());
      c->VpiColumnNo(rhs->VpiColumnNo());
      c->VpiEndLineNo(rhs->VpiEndLineNo());
      c->VpiEndColumnNo(rhs->VpiEndColumnNo());
      result = c;
      uint64_t value = 0;
      for (uint64_t i = 0; i < patternSize; i++) {
        value |= (values[i]) ? ((uint64_t)1 << (patternSize - 1 - i)) : 0;
      }
      result->VpiSize(size);
      result->VpiValue("UINT:" + std::to_string(value));
      result->VpiDecompile(std::to_string(size) + "\'d" +
                           std::to_string(value));
    }
  } else if (tps->UhdmType() == uhdmstruct_typespec) {
    if (!invalidValue) {
      result = rhs;
    }
  }
  return result;
}

bool CompileHelper::valueRange(Value* val, const UHDM::typespec* lhstps,
                               const UHDM::typespec* rhstps,
                               DesignComponent* component,
                               CompileDesign* compileDesign,
                               ValuedComponentI* instance) {
  if (!lhstps || !rhstps) return false;
  range* r = nullptr;
  UHDM_OBJECT_TYPE type = lhstps->UhdmType();
  switch (type) {
    case uhdmlogic_typespec: {
      logic_typespec* lts = (logic_typespec*)lhstps;
      if (lts->Ranges() && !lts->Ranges()->empty()) {
        r = (*lts->Ranges())[0];
      }
      break;
    }
    case uhdmarray_typespec: {
      array_typespec* lts = (array_typespec*)lhstps;
      if (lts->Ranges() && !lts->Ranges()->empty()) {
        r = (*lts->Ranges())[0];
      }
      break;
    }
    case uhdmpacked_array_typespec: {
      packed_array_typespec* lts = (packed_array_typespec*)lhstps;
      if (lts->Ranges() && !lts->Ranges()->empty()) {
        r = (*lts->Ranges())[0];
      }
      break;
    }
    case uhdmbit_typespec: {
      bit_typespec* lts = (bit_typespec*)lhstps;
      if (lts->Ranges() && !lts->Ranges()->empty()) {
        r = (*lts->Ranges())[0];
      }
      break;
    }
    case uhdmint_typespec: {
      int_typespec* lts = (int_typespec*)lhstps;
      if (lts->Ranges() && !lts->Ranges()->empty()) {
        r = (*lts->Ranges())[0];
      }
      break;
    }
    default:
      break;
  }
  bool isSigned = false;
  type = rhstps->UhdmType();
  switch (type) {
    case uhdmlogic_typespec: {
      logic_typespec* tps = (logic_typespec*)rhstps;
      isSigned = tps->VpiSigned();
      break;
    }
    case uhdmbit_typespec: {
      bit_typespec* tps = (bit_typespec*)rhstps;
      isSigned = tps->VpiSigned();
      break;
    }
    case uhdmint_typespec: {
      int_typespec* tps = (int_typespec*)rhstps;
      isSigned = tps->VpiSigned();
      break;
    }
    default:
      break;
  }
  if (r) {
    bool invalidValue = false;
    expr* lv = reduceExpr((any*)r->Left_expr(), invalidValue, component,
                          compileDesign, instance, BadPathId, 0, nullptr, true);
    expr* rv = reduceExpr((any*)r->Right_expr(), invalidValue, component,
                          compileDesign, instance, BadPathId, 0, nullptr, true);
    UHDM::ExprEval eval;
    int64_t lvv = eval.get_value(invalidValue, lv);
    int64_t rvv = eval.get_value(invalidValue, rv);
    if (invalidValue == false) {
      val->setRange(lvv, rvv);
    }
  }
  val->setSigned(isSigned);
  return false;
}

void CompileHelper::setRange(UHDM::constant* c, Value* val,
                             CompileDesign* compileDesign) {
  if (!val || !c) return;
  Serializer& s = compileDesign->getSerializer();
  uint16_t lr = val->getLRange();
  uint16_t rr = val->getRRange();
  if (lr || rr) {
    logic_typespec* tps = s.MakeLogic_typespec();
    ref_typespec* tpsRef = s.MakeRef_typespec();
    tpsRef->VpiParent(c);
    tpsRef->Actual_typespec(tps);
    c->Typespec(tpsRef);
    range* r = s.MakeRange();
    r->VpiParent(tps);
    VectorOfrange* ranges = s.MakeRangeVec();
    ranges->push_back(r);
    tps->Ranges(ranges);
    constant* lc = s.MakeConstant();
    lc->VpiValue("UINT:" + std::to_string(lr));
    r->Left_expr(lc);
    constant* rc = s.MakeConstant();
    rc->VpiValue("UINT:" + std::to_string(rr));
    r->Right_expr(rc);
  }
}

void CompileHelper::compileLetDeclaration(DesignComponent* component,
                                          const FileContent* fC,
                                          NodeId Let_declaration,
                                          CompileDesign* compileDesign) {
  Serializer& s = compileDesign->getSerializer();
  NodeId nameId = fC->Child(Let_declaration);
  const std::string_view name = fC->SymName(nameId);
  NodeId Let_port_list = fC->Sibling(nameId);
  NodeId Expression;
  if (fC->Type(Let_port_list) == VObjectType::paLet_port_list) {
    Expression = fC->Sibling(Let_port_list);
  } else {
    Expression = Let_port_list;
  }
  auto ios =
      compileTfPortList(component, nullptr, fC, Let_port_list, compileDesign);
  component->lateBinding(false);
  let_decl* decl = s.MakeLet_decl();
  decl->VpiName(name);
  fC->populateCoreMembers(Let_declaration, Let_declaration, decl);
  expr* exp = (expr*)compileExpression(component, fC, Expression, compileDesign,
                                       Reduce::No, decl, nullptr, false);
  component->lateBinding(true);
  VectorOfexpr* exprs = s.MakeExprVec();
  exprs->push_back(exp);
  decl->Expressions(exprs);
  VectorOfseq_formal_decl* args = s.MakeSeq_formal_declVec();
  for (auto io : *ios) {
    seq_formal_decl* formal = s.MakeSeq_formal_decl();
    formal->VpiName(io->VpiName());
    formal->VpiParent(exp);
    args->push_back(formal);
  }
  LetStmt* stmt = new LetStmt(decl, args, exp);
  component->insertLetStmt(name, stmt);
}

bool CompileHelper::elaborationSystemTask(DesignComponent* component,
                                          const FileContent* fC, NodeId id,
                                          CompileDesign* compileDesign) {
  NodeId taskNameId = fC->Child(id);
  NodeId NumberOrArgList = fC->Sibling(taskNameId);
  NodeId ArgList = NumberOrArgList;
  if (fC->Type(ArgList) != VObjectType::paList_of_arguments) {
    ArgList = fC->Sibling(ArgList);
  }
  NodeId Expression = fC->Child(ArgList);
  NodeId Primary = fC->Child(Expression);
  NodeId Primary_literal = fC->Child(Primary);
  NodeId StringId = fC->Child(Primary_literal);
  std::string_view text = fC->SymName(StringId);
  std::string_view name = fC->SymName(taskNameId);
  Serializer& s = compileDesign->getSerializer();
  UHDM::sys_task_call* scall = s.MakeSys_task_call();
  fC->populateCoreMembers(id, id, scall);
  scall->VpiName(name);
  VectorOfany* args = s.MakeAnyVec();
  scall->Tf_call_args(args);
  constant* c = s.MakeConstant();
  args->push_back(c);
  c->VpiValue(std::string("STRING:") + std::string(text));
  c->VpiDecompile(text);
  c->VpiConstType(vpiStringConst);
  component->addElabSysCall(scall);
  Location loc(fC->getFileId(id), fC->Line(id), fC->Column(id),
               m_symbols->registerSymbol(text));
  if (name == "fatal") {
    Error err(ErrorDefinition::ELAB_SYSTEM_FATAL, loc);
    m_errors->addError(err);
  } else if (name == "error") {
    Error err(ErrorDefinition::ELAB_SYSTEM_ERROR, loc);
    m_errors->addError(err);
  }
  if (name == "warning") {
    Error err(ErrorDefinition::ELAB_SYSTEM_WARNING, loc);
    m_errors->addError(err);
  }
  if (name == "info") {
    Error err(ErrorDefinition::ELAB_SYSTEM_INFO, loc);
    m_errors->addError(err);
  }
  return true;
}

}  // namespace SURELOG
