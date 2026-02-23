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
 * File:   CompileExpression.cpp
 * Author: alain
 *
 * Created on May 14, 2019, 8:03 PM
 */

#include <uhdm/BaseClass.h>
#include <uhdm/expr.h>
#include <uhdm/uhdm_types.h>

#include <algorithm>
#include <cmath>
#include <cstdint>
#include <cstring>
#include <iostream>
#include <set>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "Surelog/CommandLine/CommandLineParser.h"
#include "Surelog/Common/FileSystem.h"
#include "Surelog/Common/NodeId.h"
#include "Surelog/Common/PathId.h"
#include "Surelog/Design/DataType.h"
#include "Surelog/Design/Enum.h"
#include "Surelog/Design/FileContent.h"
#include "Surelog/Design/ModuleDefinition.h"
#include "Surelog/Design/ModuleInstance.h"
#include "Surelog/Design/Netlist.h"
#include "Surelog/Design/ParamAssign.h"
#include "Surelog/Design/Parameter.h"
#include "Surelog/Design/SimpleType.h"
#include "Surelog/Design/Struct.h"
#include "Surelog/Design/TimeInfo.h"
#include "Surelog/Design/Union.h"
#include "Surelog/Design/ValuedComponentI.h"
#include "Surelog/DesignCompile/CompileDesign.h"
#include "Surelog/DesignCompile/CompileHelper.h"
#include "Surelog/DesignCompile/UhdmWriter.h"
#include "Surelog/ErrorReporting/Error.h"
#include "Surelog/ErrorReporting/ErrorDefinition.h"
#include "Surelog/ErrorReporting/Location.h"
#include "Surelog/Package/Package.h"
#include "Surelog/SourceCompile/Compiler.h"
#include "Surelog/SourceCompile/SymbolTable.h"
#include "Surelog/SourceCompile/VObjectTypes.h"
#include "Surelog/Testbench/TypeDef.h"
#include "Surelog/Utils/NumUtils.h"
#include "Surelog/Utils/StringUtils.h"

// UHDM
#include <uhdm/ElaboratorListener.h>
#include <uhdm/ExprEval.h>
#include <uhdm/clone_tree.h>
#include <uhdm/sv_vpi_user.h>
#include <uhdm/uhdm.h>
#include <uhdm/vpi_user.h>
#include <uhdm/vpi_visitor.h>

namespace SURELOG {

using namespace UHDM;  // NOLINT (using a bunch of them)

bool CompileHelper::substituteAssignedValue(const UHDM::any *oper,
                                            CompileDesign *compileDesign) {
  bool substitute = true;
  if (!oper) {
    return false;
  }
  UHDM_OBJECT_TYPE opType = oper->UhdmType();
  if (opType == uhdmoperation) {
    operation *op = (operation *)oper;
    int32_t opType = op->VpiOpType();
    if (opType == vpiAssignmentPatternOp || opType == vpiConcatOp) {
      substitute = compileDesign->getCompiler()
                       ->getCommandLineParser()
                       ->getParametersSubstitution();
    }
    for (auto operand : *op->Operands()) {
      if (!substituteAssignedValue(operand, compileDesign)) {
        return false;
      }
    }
  }
  return substitute;
}

any *CompileHelper::getObject(std::string_view name, DesignComponent *component,
                              CompileDesign *compileDesign,
                              ValuedComponentI *instance, const any *pexpr) {
  any *result = nullptr;
  while (pexpr) {
    if (const UHDM::scope *s = any_cast<const scope *>(pexpr)) {
      if ((result == nullptr) && s->Variables()) {
        for (auto o : *s->Variables()) {
          if (o->VpiName() == name) {
            result = o;
            break;
          }
        }
      }
    }
    if (const UHDM::task_func *s = any_cast<const task_func *>(pexpr)) {
      if ((result == nullptr) && s->Io_decls()) {
        for (auto o : *s->Io_decls()) {
          if (o->VpiName() == name) {
            result = o;
            break;
          }
        }
      }
    }
    if (result) break;
    pexpr = pexpr->VpiParent();
  }
  if ((result == nullptr) && instance) {
    if (ModuleInstance *inst =
            valuedcomponenti_cast<ModuleInstance *>(instance)) {
      while (inst) {
        Netlist *netlist = inst->getNetlist();
        if (netlist) {
          if ((result == nullptr) && netlist->array_nets()) {
            for (auto o : *netlist->array_nets()) {
              if (o->VpiName() == name) {
                result = o;
                break;
              }
            }
          }
          if ((result == nullptr) && netlist->nets()) {
            for (auto o : *netlist->nets()) {
              if (o->VpiName() == name) {
                result = o;
                break;
              }
            }
          }
          if ((result == nullptr) && netlist->variables()) {
            for (auto o : *netlist->variables()) {
              if (o->VpiName() == name) {
                result = o;
                break;
              }
            }
          }
          if ((result == nullptr) && netlist->ports()) {
            for (auto o : *netlist->ports()) {
              if (o->VpiName() == name) {
                result = o;
                break;
              }
            }
          }
          if ((result == nullptr) && netlist->param_assigns()) {
            for (auto o : *netlist->param_assigns()) {
              const std::string_view pname = o->Lhs()->VpiName();
              if (pname == name) {
                result = o;
                break;
              }
            }
          }
        }
        if ((result == nullptr) ||
            (result && (result->UhdmType() != uhdmconstant) &&
             (result->UhdmType() != uhdmparam_assign))) {
          if (expr *complex = instance->getComplexValue(name)) {
            result = complex;
          }
        }
        if (result) break;
        if (inst) {
          VObjectType insttype = inst->getType();
          if ((insttype != VObjectType::paInterface_instantiation) &&
              (insttype != VObjectType::paConditional_generate_construct) &&
              (insttype != VObjectType::paLoop_generate_construct) &&
              (insttype != VObjectType::paGenerate_item) &&
              (insttype !=
               VObjectType::paGenerate_module_conditional_statement) &&
              (insttype !=
               VObjectType::paGenerate_interface_conditional_statement) &&
              (insttype != VObjectType::paGenerate_module_loop_statement) &&
              (insttype != VObjectType::paGenerate_interface_loop_statement) &&
              (insttype != VObjectType::paGenerate_module_named_block) &&
              (insttype != VObjectType::paGenerate_interface_named_block) &&
              (insttype != VObjectType::paGenerate_module_block) &&
              (insttype != VObjectType::paGenerate_interface_block) &&
              (insttype != VObjectType::paGenerate_module_item) &&
              (insttype != VObjectType::paGenerate_interface_item) &&
              (insttype != VObjectType::paGenerate_begin_end_block)) {
            break;
          } else {
            inst = inst->getParent();
          }
        }
      }
    }
  }
  // Instance component or package component
  if ((result == nullptr) && component) {
    for (ParamAssign *pass : component->getParamAssignVec()) {
      if (param_assign *p = pass->getUhdmParamAssign()) {
        const std::string_view pname = p->Lhs()->VpiName();
        if (pname == name) {
          if (substituteAssignedValue(p->Rhs(), compileDesign)) {
            result = p->Rhs();
            break;
          }
        }
      }
    }
    const DataType *dtype = component->getDataType(name);
    if ((result == nullptr) && dtype) {
      dtype = dtype->getActual();
      if (dtype->getTypespec()) result = dtype->getTypespec();
    }

    Signal *sig = nullptr;
    for (auto s : component->getPorts()) {
      if (s->getName() == name) {
        sig = s;
        break;
      }
    }
    if (sig == nullptr) {
      for (auto s : component->getSignals()) {
        if (s->getName() == name) {
          sig = s;
          break;
        }
      }
    }
    if (sig) {
      if (sig->getTypeSpecId()) {
        result = compileTypespec(component, sig->getFileContent(),
                                 sig->getTypeSpecId(), compileDesign,
                                 Reduce::No, nullptr, instance, true);
      }
    }
  }

  if ((result == nullptr) && instance) {
    if (ModuleInstance *inst =
            valuedcomponenti_cast<ModuleInstance *>(instance)) {
      // Instance component
      if (DesignComponent *comp = inst->getDefinition()) {
        for (ParamAssign *pass : comp->getParamAssignVec()) {
          if (param_assign *p = pass->getUhdmParamAssign()) {
            const std::string_view pname = p->Lhs()->VpiName();
            if (pname == name) {
              if (substituteAssignedValue(p->Rhs(), compileDesign)) {
                result = p->Rhs();
                break;
              }
            }
          }
        }

        const DataType *dtype = comp->getDataType(name);
        if ((result == nullptr) && dtype) {
          dtype = dtype->getActual();
          if (dtype->getTypespec()) result = dtype->getTypespec();
        }
      }
    }
  }

  if (result && (result->UhdmType() == uhdmref_obj)) {
    ref_obj *ref = (ref_obj *)result;
    const std::string_view refname = ref->VpiName();
    if (refname != name)
      result = getObject(refname, component, compileDesign, instance, pexpr);
    if (result) {
      if (UHDM::param_assign *passign = any_cast<param_assign *>(result)) {
        result = passign->Rhs();
      }
    }
  }
  if (result && result->UhdmType() == uhdmconstant) {
    if (instance) {
      Value *sval = instance->getValue(name);
      if (sval && sval->isValid()) {
        setRange((constant *)result, sval, compileDesign);
      }
    }
  }
  return result;
}

UHDM::task_func *getFuncFromPackage(std::string_view name,
                                    DesignComponent *component,
                                    std::set<DesignComponent *> &visited) {
  for (Package *pack : component->getAccessPackages()) {
    if (pack->getTask_funcs()) {
      for (UHDM::task_func *tf : *pack->getTask_funcs()) {
        if (tf->VpiName() == name) {
          return tf;
        }
      }
    }
    if (visited.find(pack) == visited.end()) {
      visited.insert(pack);
      UHDM::task_func *res = getFuncFromPackage(name, pack, visited);
      if (res) {
        return res;
      }
    }
  }
  return nullptr;
}

std::pair<UHDM::task_func *, DesignComponent *> CompileHelper::getTaskFunc(
    std::string_view name, DesignComponent *component,
    CompileDesign *compileDesign, ValuedComponentI *instance, any *pexpr) {
  std::pair<UHDM::task_func *, DesignComponent *> result = {nullptr, nullptr};
  DesignComponent *comp = component;
  if (name.find("::") != std::string::npos) {
    std::vector<std::string_view> res;
    StringUtils::tokenizeMulti(name, "::", res);
    if (res.size() > 1) {
      const std::string_view packName = res[0];
      const std::string_view funcName = res[1];
      Design *design = compileDesign->getCompiler()->getDesign();
      if (Package *pack = design->getPackage(packName)) {
        if (pack->getTask_funcs()) {
          for (UHDM::task_func *tf : *pack->getTask_funcs()) {
            if (tf->VpiName() == funcName) {
              result = std::make_pair(tf, pack);
              return result;
            }
          }
        }
      }
    }
  }
  while (comp) {
    if (comp->getTask_funcs()) {
      for (UHDM::task_func *tf : *comp->getTask_funcs()) {
        if (tf->VpiName() == name) {
          result = std::make_pair(tf, component);
          return result;
        }
      }
    }
    comp = valuedcomponenti_cast<DesignComponent *>(
        (DesignComponent *)comp->getParentScope());
  }
  if (component) {
    for (const FileContent *cfC : component->getFileContents()) {
      FileContent *fC = (FileContent *)cfC;
      if (fC->getTask_funcs()) {
        for (UHDM::task_func *tf : *fC->getTask_funcs()) {
          if (tf->VpiName() == name) {
            result = std::make_pair(tf, component);
            return result;
          }
        }
      }
    }
  }
  if (component) {
    std::set<DesignComponent *> visited;
    task_func *res = getFuncFromPackage(name, component, visited);
    if (res) {
      result = std::make_pair(res, component);
      return result;
    }
  }
  if (instance) {
    ModuleInstance *inst = valuedcomponenti_cast<ModuleInstance *>(instance);
    while (inst) {
      DesignComponent *def = inst->getDefinition();
      if (def) {
        if (def->getTask_funcs()) {
          for (UHDM::task_func *tf : *def->getTask_funcs()) {
            if (tf->VpiName() == name) {
              result = std::make_pair(tf, def);
              return result;
            }
          }
        }
      }
      inst = inst->getParent();
    }
  }
  Design *design = compileDesign->getCompiler()->getDesign();
  auto &all_files = design->getAllFileContents();
  for (const auto &file : all_files) {
    FileContent *fC = file.second;
    if (fC->getTask_funcs()) {
      for (UHDM::task_func *tf : *fC->getTask_funcs()) {
        if (tf->VpiName() == name) {
          result = std::make_pair(tf, component);
          return result;
        }
      }
    }
  }
  return result;
}

static bool largeInt(std::string_view str) {
  bool isSigned = false;
  size_t pos = str.find('\'');
  if (pos != std::string::npos) {
    if (str.find_first_of("sS") != std::string::npos) {
      isSigned = true;
      str = str.substr(pos + 3);
    } else {
      str = str.substr(pos + 2);
    }
  }
  std::string value(str);
  value = StringUtils::replaceAll(value, "_", "");
  bool isLarge = false;
  if (value.size() > 20) {
    isLarge = true;
  } else if (value.size() == 20) {
    if (isSigned) {
      int64_t test = 0;
      isLarge = NumUtils::parseInt64(value, &test) == nullptr;
    } else {
      uint64_t test = 0;
      isLarge = NumUtils::parseUint64(value, &test) == nullptr;
    }
  }
  return isLarge;
}

constant *compileConst(const FileContent *fC, NodeId child, Serializer &s) {
  VObjectType objtype = fC->Type(child);
  constant *result = nullptr;
  switch (objtype) {
    case VObjectType::slIntConst: {
      // Do not evaluate the constant, keep it as in the source text:
      UHDM::constant *c = s.MakeConstant();
      fC->populateCoreMembers(child, child, c);
      std::string value = std::string(fC->SymName(child));
      value.erase(std::remove(value.begin(), value.end(), '_'), value.end());
      std::string v;
      c->VpiDecompile(value);
      bool tickNumber = (value.find('\'') != std::string::npos);
      if (tickNumber || largeInt(value)) {
        char base = 'd';
        uint32_t i = 0;
        bool isSigned = false;
        std::string size(value);
        if (tickNumber) {
          for (i = 0; i < value.size(); i++) {
            if (value[i] == '\'') {
              base = value[i + 1];
              if (base == 's' || base == 'S') base = value[i + 2];
              break;
            }
          }
          if (value.find_first_of("sS") != std::string::npos) {
            isSigned = true;
            v = value.substr(i + 3);
          } else {
            v = value.substr(i + 2);
          }
        } else {
          v = value;
          size = "";
        }
        v = StringUtils::replaceAll(v, "#", "");
        v = StringUtils::replaceAll(v, "_", "");
        size = StringUtils::rtrim_until(size, '\'');
        if (size.empty()) {
          c->VpiSize(-1);
        } else {
          int32_t s = 0;
          if (NumUtils::parseInt32(size, &s) == nullptr) {
            s = 0;
          }
          c->VpiSize(s);
        }
        if (isSigned) {
          int_typespec *tps = s.MakeInt_typespec();
          tps->VpiSigned(true);
          ref_typespec *const rt = s.MakeRef_typespec();
          rt->VpiParent(c);
          c->Typespec(rt);
          rt->Actual_typespec(tps);
        }
        switch (base) {
          case 'h':
          case 'H': {
            v = "HEX:" + v;
            c->VpiConstType(vpiHexConst);
            break;
          }
          case 'b':
          case 'B': {
            v = "BIN:" + v;
            c->VpiConstType(vpiBinaryConst);
            break;
          }
          case 'o':
          case 'O': {
            v = "OCT:" + v;
            c->VpiConstType(vpiOctConst);
            break;
          }
          case 'd':
          case 'D': {
            v = "DEC:" + v;
            c->VpiConstType(vpiDecConst);
            break;
          }
          default: {
            v = "BIN:" + v;
            c->VpiConstType(vpiBinaryConst);
            break;
          }
        }
      } else {
        if (!value.empty() && value[0] == '-') {
          v.assign("INT:").append(value);
          c->VpiConstType(vpiIntConst);
        } else {
          v.assign("UINT:").append(value);
          c->VpiConstType(vpiUIntConst);
          v = StringUtils::replaceAll(v, "#", "");
        }
        c->VpiSize(64);
      }

      c->VpiValue(v);
      result = c;
      break;
    }
    case VObjectType::slRealConst: {
      UHDM::constant *c = s.MakeConstant();
      const std::string_view value = fC->SymName(child);
      c->VpiDecompile(value);
      c->VpiValue(StrCat("REAL:", value));
      c->VpiConstType(vpiRealConst);
      c->VpiSize(64);
      result = c;
      break;
    }
    case VObjectType::paNumber_1Tickb1:
    case VObjectType::paNumber_1TickB1:
    case VObjectType::paInitVal_1Tickb1:
    case VObjectType::paInitVal_1TickB1:
    case VObjectType::paScalar_1Tickb1:
    case VObjectType::paScalar_1TickB1:
    case VObjectType::pa1: {
      UHDM::constant *c = s.MakeConstant();
      std::string value = "BIN:1";
      c->VpiValue(value);
      c->VpiConstType(vpiBinaryConst);
      c->VpiSize(1);
      c->VpiDecompile("1'b1");
      fC->populateCoreMembers(child, child, c);
      result = c;
      break;
    }
    case VObjectType::paScalar_Tickb1:
    case VObjectType::paScalar_TickB1:
    case VObjectType::paNumber_Tickb1:
    case VObjectType::paNumber_TickB1: {
      UHDM::constant *c = s.MakeConstant();
      std::string value = "BIN:1";
      c->VpiValue(value);
      c->VpiConstType(vpiBinaryConst);
      c->VpiSize(0);
      c->VpiDecompile("'b1");
      result = c;
      break;
    }
    case VObjectType::paNumber_Tick1: {
      UHDM::constant *c = s.MakeConstant();
      std::string value = "BIN:1";
      c->VpiValue(value);
      c->VpiConstType(vpiBinaryConst);
      c->VpiSize(-1);
      c->VpiDecompile("'1");
      result = c;
      break;
    }
    case VObjectType::paNumber_1Tickb0:
    case VObjectType::paNumber_1TickB0:
    case VObjectType::paInitVal_1Tickb0:
    case VObjectType::paInitVal_1TickB0:
    case VObjectType::paScalar_1Tickb0:
    case VObjectType::paScalar_1TickB0:
    case VObjectType::pa0: {
      UHDM::constant *c = s.MakeConstant();
      std::string value = "BIN:0";
      c->VpiValue(value);
      c->VpiConstType(vpiBinaryConst);
      c->VpiSize(1);
      c->VpiDecompile("1'b0");
      fC->populateCoreMembers(child, child, c);
      result = c;
      break;
    }
    case VObjectType::paScalar_Tickb0:
    case VObjectType::paScalar_TickB0:
    case VObjectType::paNumber_Tickb0:
    case VObjectType::paNumber_TickB0: {
      UHDM::constant *c = s.MakeConstant();
      std::string value = "BIN:0";
      c->VpiValue(value);
      c->VpiConstType(vpiBinaryConst);
      c->VpiSize(0);
      c->VpiDecompile("'b0");
      fC->populateCoreMembers(child, child, c);
      result = c;
      break;
    }
    case VObjectType::paNumber_Tick0: {
      UHDM::constant *c = s.MakeConstant();
      std::string value = "BIN:0";
      c->VpiValue(value);
      c->VpiConstType(vpiBinaryConst);
      c->VpiSize(-1);
      c->VpiDecompile("'0");
      fC->populateCoreMembers(child, child, c);
      result = c;
      break;
    }
    case VObjectType::paZ: {
      UHDM::constant *c = s.MakeConstant();
      std::string value = "BIN:Z";
      c->VpiValue(value);
      c->VpiConstType(vpiBinaryConst);
      c->VpiSize(-1);
      c->VpiDecompile("'Z");
      result = c;
      break;
    }
    case VObjectType::paX: {
      UHDM::constant *c = s.MakeConstant();
      std::string value = "BIN:X";
      c->VpiValue(value);
      c->VpiConstType(vpiBinaryConst);
      c->VpiSize(-1);
      c->VpiDecompile("'X");
      result = c;
      break;
    }
    case VObjectType::paNumber_1TickBX:
    case VObjectType::paNumber_1TickbX:
    case VObjectType::paNumber_1Tickbx:
    case VObjectType::paNumber_1TickBx:
    case VObjectType::paInitVal_1Tickbx:
    case VObjectType::paInitVal_1TickbX:
    case VObjectType::paInitVal_1TickBx:
    case VObjectType::paInitVal_1TickBX: {
      UHDM::constant *c = s.MakeConstant();
      std::string value = "BIN:X";
      c->VpiValue(value);
      c->VpiConstType(vpiBinaryConst);
      c->VpiSize(1);
      c->VpiDecompile("1'bX");
      result = c;
      break;
    }
    case VObjectType::paTime_literal: {
      NodeId intC = fC->Child(child);
      const std::string_view value = fC->SymName(intC);
      NodeId unitId = fC->Sibling(intC);
      TimeInfo::Unit unit = TimeInfo::unitFromString(fC->SymName(unitId));
      uint64_t val = 0;
      if (NumUtils::parseUint64(value, &val) == nullptr) {
        val = 0;
      }
      switch (unit) {
        case TimeInfo::Unit::Second: {
          val = 1e12 * val;
          break;
        }
        case TimeInfo::Unit::Millisecond: {
          val = 1e9 * val;
          break;
        }
        case TimeInfo::Unit::Nanosecond: {
          val = 1e6 * val;
          break;
        }
        case TimeInfo::Unit::Microsecond: {
          val = 1e3 * val;
          break;
        }
        case TimeInfo::Unit::Picosecond: {
          val = 1 * val;
          break;
        }
        case TimeInfo::Unit::Femtosecond: {
          val = 1e-3 * val;
          break;
        }
        default:
          break;
      }
      UHDM::constant *c = s.MakeConstant();
      c->VpiValue("UINT:" + std::to_string(val));
      c->VpiConstType(vpiUIntConst);
      c->VpiSize(64);
      result = c;
      break;
    }
    case VObjectType::slStringLiteral: {
      UHDM::constant *c = s.MakeConstant();
      std::string_view value = StringUtils::unquoted(fC->SymName(child));
      c->VpiDecompile(fC->SymName(child));
      c->VpiSize(value.length() * 8);
      c->VpiValue(StrCat("STRING:", value));
      c->VpiConstType(vpiStringConst);
      result = c;
      break;
    }
    default:
      break;
  }
  return result;
}

any *CompileHelper::decodeHierPath(hier_path *path, bool &invalidValue,
                                   DesignComponent *component,
                                   CompileDesign *compileDesign, Reduce reduce,
                                   ValuedComponentI *instance, PathId fileId,
                                   uint32_t lineNumber, any *pexpr,
                                   bool muteErrors, bool returnTypespec) {
  UHDM::GetObjectFunctor getObjectFunctor =
      [&](std::string_view name, const any *inst,
          const any *pexpr) -> UHDM::any * {
    return getObject(name, component, compileDesign, instance, pexpr);
  };
  UHDM::GetObjectFunctor getValueFunctor =
      [&](std::string_view name, const any *inst,
          const any *pexpr) -> UHDM::any * {
    return (expr *)getValue(name, component, compileDesign, Reduce::Yes,
                            instance, fileId, lineNumber, (any *)pexpr, false);
  };
  UHDM::GetTaskFuncFunctor getTaskFuncFunctor =
      [&](std::string_view name, const any *inst) -> UHDM::task_func * {
    auto ret = getTaskFunc(name, component, compileDesign, instance, pexpr);
    return ret.first;
  };
  UHDM::ExprEval eval(muteErrors);
  eval.setGetObjectFunctor(getObjectFunctor);
  eval.setGetValueFunctor(getValueFunctor);
  eval.setGetTaskFuncFunctor(getTaskFuncFunctor);
  if (m_exprEvalPlaceHolder == nullptr) {
    m_exprEvalPlaceHolder = compileDesign->getSerializer().MakeModule_inst();
    m_exprEvalPlaceHolder->Param_assigns(
        compileDesign->getSerializer().MakeParam_assignVec());
  } else {
    m_exprEvalPlaceHolder->Param_assigns()->erase(
        m_exprEvalPlaceHolder->Param_assigns()->begin(),
        m_exprEvalPlaceHolder->Param_assigns()->end());
  }
  any *res =
      eval.decodeHierPath(path, invalidValue, m_exprEvalPlaceHolder, pexpr,
                          returnTypespec ? UHDM::ExprEval::ReturnType::TYPESPEC
                                         : UHDM::ExprEval::ReturnType::VALUE,
                          muteErrors);

  if (res == nullptr) {
    if ((reduce == Reduce::Yes) && (!muteErrors)) {
      ErrorContainer *errors =
          compileDesign->getCompiler()->getErrorContainer();
      SymbolTable *symbols = compileDesign->getCompiler()->getSymbolTable();
      // std::string fileContent = FileUtils::getFileContent(fileName);
      // std::string_view lineText =
      //     StringUtils::getLineInString(fileContent, lineNumber);
      const std::string_view lineText = path->VpiFullName();
      Location loc(fileId, lineNumber, 0, symbols->registerSymbol(lineText));
      Error err(ErrorDefinition::UHDM_UNRESOLVED_HIER_PATH, loc);
      errors->addError(err);
    }
  }
  return res;
}

expr *CompileHelper::reduceExpr(any *result, bool &invalidValue,
                                DesignComponent *component,
                                CompileDesign *compileDesign,
                                ValuedComponentI *instance, PathId fileId,
                                uint32_t lineNumber, any *pexpr,
                                bool muteErrors) {
  UHDM::GetObjectFunctor getObjectFunctor =
      [&](std::string_view name, const any *inst,
          const any *pexpr) -> UHDM::any * {
    return getObject(name, component, compileDesign, instance, pexpr);
  };
  UHDM::GetObjectFunctor getValueFunctor =
      [&](std::string_view name, const any *inst,
          const any *pexpr) -> UHDM::any * {
    return (expr *)getValue(name, component, compileDesign, Reduce::Yes,
                            instance, fileId, lineNumber, (any *)pexpr,
                            muteErrors);
  };
  UHDM::GetTaskFuncFunctor getTaskFuncFunctor =
      [&](std::string_view name, const any *inst) -> UHDM::task_func * {
    auto ret = getTaskFunc(name, component, compileDesign, instance, pexpr);
    return ret.first;
  };
  UHDM::ExprEval eval(muteErrors);
  eval.setGetObjectFunctor(getObjectFunctor);
  eval.setGetValueFunctor(getValueFunctor);
  eval.setGetTaskFuncFunctor(getTaskFuncFunctor);
  if (m_exprEvalPlaceHolder == nullptr) {
    m_exprEvalPlaceHolder = compileDesign->getSerializer().MakeModule_inst();
    m_exprEvalPlaceHolder->Param_assigns(
        compileDesign->getSerializer().MakeParam_assignVec());
  } else {
    m_exprEvalPlaceHolder->Param_assigns()->erase(
        m_exprEvalPlaceHolder->Param_assigns()->begin(),
        m_exprEvalPlaceHolder->Param_assigns()->end());
  }
  expr *res = eval.reduceExpr(result, invalidValue, m_exprEvalPlaceHolder,
                              pexpr, muteErrors);
  // If loop was detected, drop the partially constructed new value!
  return m_unwind ? nullptr : res;
}

any *CompileHelper::getValue(std::string_view name, DesignComponent *component,
                             CompileDesign *compileDesign, Reduce reduce,
                             ValuedComponentI *instance, PathId fileId,
                             uint32_t lineNumber, any *pexpr, bool muteErrors) {
  Serializer &s = compileDesign->getSerializer();
  Value *sval = nullptr;
  any *result = nullptr;
  if (loopDetected(fileId, lineNumber, compileDesign, instance)) {
    return nullptr;
  }
  if (m_checkForLoops) {
    m_stackLevel++;
  }
  if (name.find("::") != std::string::npos) {
    std::vector<std::string_view> res;
    StringUtils::tokenizeMulti(name, "::", res);
    if (res.size() > 1) {
      const std::string_view packName = res[0];
      const std::string_view varName = res[1];
      Design *design = compileDesign->getCompiler()->getDesign();
      if (Package *pack = design->getPackage(packName)) {
        if (expr *val = pack->getComplexValue(varName)) {
          result = val;
          if (result && (result->UhdmType() == uhdmoperation)) {
            operation *op = (operation *)result;
            const UHDM::typespec *opts = nullptr;
            if (ref_typespec *rt = op->Typespec()) {
              opts = rt->Actual_typespec();
            }
            UHDM::ExprEval eval;
            if (expr *res = eval.flattenPatternAssignments(
                    s, opts, (UHDM::expr *)result)) {
              if (res->UhdmType() == uhdmoperation) {
                op->Operands(((operation *)res)->Operands());
              }
            }
          }
        }
        if (result == nullptr) {
          if (Value *sval = pack->getValue(varName)) {
            UHDM::constant *c = s.MakeConstant();
            c->VpiValue(sval->uhdmValue());
            setRange(c, sval, compileDesign);
            c->VpiDecompile(sval->decompiledValue());
            c->VpiConstType(sval->vpiValType());
            c->VpiSize(sval->getSize());
            result = c;
          }
        }

        if (UHDM::VectorOfparam_assign *param_assigns =
                pack->getParam_assigns()) {
          for (param_assign *param : *param_assigns) {
            if (param && param->Lhs()) {
              const std::string_view param_name = param->Lhs()->VpiName();
              if (param_name == varName) {
                if (substituteAssignedValue(param->Rhs(), compileDesign)) {
                  if (param->Rhs()->UhdmType() == uhdmoperation) {
                    operation *op = (operation *)param->Rhs();
                    int32_t opType = op->VpiOpType();
                    if (opType == vpiAssignmentPatternOp) {
                      const any *lhs = param->Lhs();
                      any *rhs = param->Rhs();
                      const typespec *ts = nullptr;
                      if (lhs->UhdmType() == uhdmparameter) {
                        if (const ref_typespec *rt =
                                ((parameter *)lhs)->Typespec()) {
                          ts = rt->Actual_typespec();
                        }
                      }
                      rhs = expandPatternAssignment(ts, (expr *)rhs, component,
                                                    compileDesign, instance);
                      param->Rhs(rhs);
                      reorderAssignmentPattern(component, lhs, rhs,
                                               compileDesign, instance, 0);
                    }
                  }

                  ElaboratorContext elaboratorContext(&s, false, true);
                  result = UHDM::clone_tree(param->Rhs(), &elaboratorContext);
                  if (result != nullptr) result->VpiParent(param);
                  break;
                }
              }
            }
          }
        }
      }
    }
  }

  if ((result == nullptr) && instance) {
    if (expr *val = instance->getComplexValue(name)) {
      result = val;
      if (result->UhdmType() == uhdmconstant) {
        sval = instance->getValue(name);
        if (sval && sval->isValid()) {
          setRange((constant *)result, sval, compileDesign);
        }
      }
    }
    if (result == nullptr) {
      sval = instance->getValue(name);
      if (sval && sval->isValid()) {
        UHDM::constant *c = s.MakeConstant();
        c->VpiValue(sval->uhdmValue());
        setRange(c, sval, compileDesign);
        c->VpiDecompile(sval->decompiledValue());
        c->VpiConstType(sval->vpiValType());
        c->VpiSize(sval->getSize());
        result = c;
      }
    }
  }

  ValuedComponentI *tmpInstance = instance;
  while ((result == nullptr) && tmpInstance) {
    if (ModuleInstance *inst =
            valuedcomponenti_cast<ModuleInstance *>(tmpInstance)) {
      Netlist *netlist = inst->getNetlist();
      if (netlist) {
        UHDM::VectorOfparam_assign *param_assigns = netlist->param_assigns();
        if (param_assigns) {
          for (param_assign *param : *param_assigns) {
            if (param && param->Lhs()) {
              const std::string_view param_name = param->Lhs()->VpiName();
              if (param_name == name) {
                if (substituteAssignedValue(param->Rhs(), compileDesign)) {
                  if (param->Rhs()->UhdmType() == uhdmoperation) {
                    operation *op = (operation *)param->Rhs();
                    int32_t opType = op->VpiOpType();
                    if (opType == vpiAssignmentPatternOp) {
                      const any *lhs = param->Lhs();
                      any *rhs = param->Rhs();
                      const typespec *ts = nullptr;
                      if (lhs->UhdmType() == uhdmparameter) {
                        if (const ref_typespec *rt =
                                ((parameter *)lhs)->Typespec()) {
                          ts = rt->Actual_typespec();
                        }
                      }
                      rhs = expandPatternAssignment(ts, (expr *)rhs, component,
                                                    compileDesign, instance);
                      param->Rhs(rhs);
                      reorderAssignmentPattern(component, lhs, rhs,
                                               compileDesign, instance, 0);
                    }
                  }

                  ElaboratorContext elaboratorContext(&s, false, true);
                  result = UHDM::clone_tree(param->Rhs(), &elaboratorContext);
                  break;
                }
              }
            }
          }
        }
        if (auto variables = netlist->variables()) {
          for (auto var : *variables) {
            if (var->VpiName() == name) {
              if (const expr *exp = var->Expr()) {
                UHDM_OBJECT_TYPE vartype = var->UhdmType();
                if (vartype == uhdmint_var || vartype == uhdminteger_var ||
                    vartype == uhdmreal_var || vartype == uhdmshort_int_var ||
                    vartype == uhdmlong_int_var)
                  result = (expr *)exp;
                break;
              }
            }
          }
        }
      }
    }
    if (result) break;
    if (ModuleInstance *inst =
            valuedcomponenti_cast<ModuleInstance *>(tmpInstance)) {
      tmpInstance = (ValuedComponentI *)inst->getParentScope();
    } else if (FScope *inst = valuedcomponenti_cast<FScope *>(tmpInstance)) {
      tmpInstance = (ValuedComponentI *)inst->getParentScope();
    } else {
      tmpInstance = nullptr;
    }
  }

  if (result == nullptr) {
    if (instance) {
      if (expr *val = instance->getComplexValue(name)) {
        result = val;
      }
      if (result == nullptr) {
        sval = instance->getValue(name);
        if (sval && sval->isValid()) {
          UHDM::constant *c = s.MakeConstant();
          c->VpiValue(sval->uhdmValue());
          setRange(c, sval, compileDesign);
          c->VpiDecompile(sval->decompiledValue());
          c->VpiConstType(sval->vpiValType());
          c->VpiSize(sval->getSize());
          result = c;
        }
      }
    }
  }

  if (component && (result == nullptr)) {
    if (expr *val = component->getComplexValue(name)) {
      result = val;
    }
    if (result == nullptr) {
      sval = component->getValue(name);
      if (sval && sval->isValid()) {
        UHDM::constant *c = s.MakeConstant();
        c->VpiValue(sval->uhdmValue());
        setRange(c, sval, compileDesign);
        c->VpiDecompile(sval->decompiledValue());
        c->VpiConstType(sval->vpiValType());
        c->VpiSize(sval->getSize());
        result = c;
      }
    }
  }

  if (component && (result == nullptr)) {
    if (UHDM::VectorOfparam_assign *param_assigns =
            component->getParam_assigns()) {
      for (param_assign *param : *param_assigns) {
        if (param && param->Lhs()) {
          const std::string_view param_name = param->Lhs()->VpiName();
          if (param_name == name) {
            if (substituteAssignedValue(param->Rhs(), compileDesign)) {
              if (param->Rhs()->UhdmType() == uhdmoperation) {
                operation *op = (operation *)param->Rhs();
                int32_t opType = op->VpiOpType();
                if (opType == vpiAssignmentPatternOp) {
                  const any *lhs = param->Lhs();
                  any *rhs = param->Rhs();
                  const typespec *ts = nullptr;
                  if (lhs->UhdmType() == uhdmparameter) {
                    if (const ref_typespec *rt =
                            ((parameter *)lhs)->Typespec()) {
                      ts = rt->Actual_typespec();
                    }
                  }
                  rhs = expandPatternAssignment(ts, (expr *)rhs, component,
                                                compileDesign, instance);
                  param->Rhs(rhs);
                  reorderAssignmentPattern(component, lhs, rhs, compileDesign,
                                           instance, 0);
                }
              }

              ElaboratorContext elaboratorContext(&s, false, true);
              result = UHDM::clone_tree(param->Rhs(), &elaboratorContext);
              if (result != nullptr) result->VpiParent(param);
              break;
            }
          }
        }
      }
    }
  }
  if (component && (result == nullptr)) {
    for (const auto &tp : component->getTypeDefMap()) {
      TypeDef *tpd = tp.second;
      typespec *tps = tpd->getTypespec();
      if (tps && tps->UhdmType() == uhdmenum_typespec) {
        enum_typespec *etps = (enum_typespec *)tps;
        for (auto n : *etps->Enum_consts()) {
          if (n->VpiName() == name) {
            UHDM::constant *c = s.MakeConstant();
            c->VpiValue(n->VpiValue());
            setRange(c, sval, compileDesign);
            c->VpiSize(64);
            c->VpiConstType(vpiUIntConst);
            result = c;
          }
        }
      }
    }
  }

  if (result) {
    UHDM_OBJECT_TYPE resultType = result->UhdmType();
    if (resultType == uhdmconstant) {
    } else if (resultType == uhdmref_obj) {
      if (result->VpiName() != name) {
        if (any *tmp = getValue(result->VpiName(), component, compileDesign,
                                Reduce::Yes, instance, fileId, lineNumber,
                                pexpr, muteErrors)) {
          result = tmp;
        }
      }
    } else if (resultType == uhdmoperation || resultType == uhdmhier_path ||
               resultType == uhdmbit_select ||
               resultType == uhdmsys_func_call) {
      if (reduce == Reduce::Yes) {
        bool invalidValue = false;
        if (any *tmp =
                reduceExpr(result, invalidValue, component, compileDesign,
                           instance, fileId, lineNumber, pexpr, muteErrors)) {
          result = tmp;
        }
      }
    } else {
      int32_t setBreakpointHere = 1;
      setBreakpointHere++;
    }
  }
  if (m_checkForLoops) {
    m_stackLevel--;
  }
  return result;
}

UHDM::any *CompileHelper::compileSelectExpression(
    DesignComponent *component, const FileContent *fC, NodeId Bit_select,
    std::string_view name, CompileDesign *compileDesign, Reduce reduce,
    UHDM::any *pexpr, ValuedComponentI *instance, bool muteErrors) {
  UHDM::Serializer &s = compileDesign->getSerializer();
  UHDM::any *result = nullptr;
  if ((fC->Type(Bit_select) == VObjectType::paConstant_bit_select) &&
      (!fC->Sibling(Bit_select))) {
    Bit_select = fC->Child(Bit_select);
  }
  if ((fC->Type(Bit_select) == VObjectType::paBit_select) &&
      (!fC->Sibling(Bit_select))) {
    Bit_select = fC->Child(Bit_select);
  }
  if (fC->Child(Bit_select) && fC->Sibling(Bit_select)) {
    // More than one
    UHDM::var_select *var_select = s.MakeVar_select();
    VectorOfexpr *exprs = s.MakeExprVec();
    var_select->Exprs(exprs);
    var_select->VpiName(name);
    if (name.find("::") != std::string::npos) {
      var_select->VpiFullName(name);
    }
    var_select->VpiParent(pexpr);
    result = var_select;
  }
  NodeId lastBitExp;
  while (Bit_select) {
    if (fC->Type(Bit_select) == VObjectType::paBit_select ||
        fC->Type(Bit_select) == VObjectType::paConstant_bit_select ||
        fC->Type(Bit_select) == VObjectType::paConstant_primary ||
        fC->Type(Bit_select) == VObjectType::paConstant_expression ||
        fC->Type(Bit_select) == VObjectType::paExpression) {
      NodeId bitexp = fC->Child(Bit_select);
      bool advanceBitSelect = false;
      if (fC->Type(Bit_select) == VObjectType::paConstant_expression) {
        bitexp = Bit_select;
        advanceBitSelect = true;
      }
      if (fC->Type(Bit_select) == VObjectType::paExpression) {
        bitexp = Bit_select;
        advanceBitSelect = true;
      }
      if (bitexp) {
        while (bitexp) {
          if ((fC->Type(bitexp) != VObjectType::paConstant_expression) &&
              (fC->Type(bitexp) != VObjectType::paExpression)) {
            break;
          }
          expr *sel =
              (expr *)compileExpression(component, fC, bitexp, compileDesign,
                                        reduce, pexpr, instance, muteErrors);

          if (result) {
            UHDM::var_select *var_select = (UHDM::var_select *)result;
            var_select->VpiParent(pexpr);
            VectorOfexpr *exprs = var_select->Exprs();
            exprs->push_back(sel);
            sel->VpiParent(var_select);
          } else if (fC->Child(Bit_select) && fC->Sibling(Bit_select)) {
            UHDM::var_select *var_select = s.MakeVar_select();
            VectorOfexpr *exprs = s.MakeExprVec();
            var_select->Exprs(exprs);
            var_select->VpiName(name);
            if (name.find("::") != std::string::npos) {
              var_select->VpiFullName(name);
            }
            var_select->VpiParent(pexpr);
            sel->VpiParent(var_select);
            exprs->push_back(sel);
            result = var_select;
          } else {
            bit_select *bit_select = s.MakeBit_select();
            bit_select->VpiName(name);
            if (name.find("::") != std::string::npos) {
              bit_select->VpiFullName(name);
            }
            bit_select->VpiIndex(sel);
            bit_select->VpiParent(pexpr);
            sel->VpiParent(bit_select);
            fC->populateCoreMembers(Bit_select, Bit_select, bit_select);
            result = bit_select;
          }
          lastBitExp = bitexp;
          if (advanceBitSelect) Bit_select = bitexp;
          bitexp = fC->Sibling(bitexp);
        }
      }
    } else if (fC->Type(Bit_select) == VObjectType::paPart_select_range ||
               fC->Type(Bit_select) ==
                   VObjectType::paConstant_part_select_range) {
      NodeId Constant_range = fC->Child(Bit_select);
      expr *sel = (expr *)compilePartSelectRange(component, fC, Constant_range,
                                                 name, compileDesign, reduce,
                                                 pexpr, instance, muteErrors);
      if (result) {
        UHDM::var_select *var_select = (UHDM::var_select *)result;
        VectorOfexpr *exprs = var_select->Exprs();
        exprs->push_back(sel);
        sel->VpiParent(var_select);
      } else if (fC->Child(Bit_select) && fC->Sibling(Bit_select)) {
        UHDM::var_select *var_select = s.MakeVar_select();
        VectorOfexpr *exprs = s.MakeExprVec();
        var_select->Exprs(exprs);
        var_select->VpiName(name);
        if (name.find("::") != std::string::npos) {
          var_select->VpiFullName(name);
        }
        var_select->VpiParent(pexpr);
        exprs->push_back(sel);
        sel->VpiParent(var_select);
      } else {
        result = sel;
      }
    } else if ((fC->Type(Bit_select) == VObjectType::slStringConst) ||
               (fC->Type(Bit_select) ==
                VObjectType::paPs_or_hierarchical_identifier)) {
      std::string hname(name);
      hier_path *path = s.MakeHier_path();
      UHDM::VectorOfany *elems = s.MakeAnyVec();
      ref_obj *r1 = s.MakeRef_obj();
      r1->VpiName(name);
      r1->VpiFullName(name);
      path->Path_elems(elems);
      elems->push_back(r1);
      r1->VpiParent(path);
      fC->populateCoreMembers(Bit_select, Bit_select, r1);
      while (Bit_select) {
        if ((fC->Type(Bit_select) ==
             VObjectType::paPs_or_hierarchical_identifier)) {
          ref_obj *r = s.MakeRef_obj();
          NodeId nameId = fC->Child(Bit_select);
          r->VpiName(fC->SymName(nameId));
          r->VpiParent(path);
          elems->push_back(r);
          hname.append(".").append(fC->SymName(nameId));
        } else if ((fC->Type(Bit_select) == VObjectType::paSelect)) {
          NodeId nameId = fC->Child(Bit_select);
          if (nameId && (fC->Type(nameId) == VObjectType::slStringConst)) {
            ref_obj *r = s.MakeRef_obj();
            r->VpiName(fC->SymName(nameId));
            r->VpiParent(path);
            elems->push_back(r);
            hname.append(".").append(fC->SymName(nameId));
          }
        } else if (fC->Type(Bit_select) == VObjectType::slStringConst) {
          NodeId tmp = fC->Sibling(Bit_select);
          if (((fC->Type(tmp) == VObjectType::paConstant_bit_select) ||
               (fC->Type(tmp) == VObjectType::paBit_select)) &&
              fC->Child(tmp)) {
            any *sel =
                compileExpression(component, fC, Bit_select, compileDesign,
                                  reduce, pexpr, instance, muteErrors);
            if (sel) {
              hname.append(".")
                  .append(sel->VpiName())
                  .append(decompileHelper(sel));
              if (sel->UhdmType() == uhdmhier_path) {
                hier_path *p = (hier_path *)sel;
                for (auto el : *p->Path_elems()) {
                  el->VpiParent(path);
                  elems->push_back(el);
                }
                break;
              } else {
                sel->VpiParent(path);
                elems->push_back(sel);
              }
            }
          } else {
            ref_obj *r2 = s.MakeRef_obj();
            r2->VpiName(fC->SymName(Bit_select));
            r2->VpiFullName(fC->SymName(Bit_select));
            r2->VpiParent(path);
            fC->populateCoreMembers(Bit_select, Bit_select, r2);
            elems->push_back(r2);
            hname.append(".").append(fC->SymName(Bit_select));
          }
        }
        Bit_select = fC->Sibling(Bit_select);
      }
      path->VpiName(hname);
      path->VpiFullName(hname);
      fC->populateCoreMembers(Bit_select, Bit_select, path);
      path->VpiParent(pexpr);
      result = path;
      break;
    }
    Bit_select = fC->Sibling(Bit_select);
    if (lastBitExp && (Bit_select == lastBitExp)) {
      Bit_select = fC->Sibling(Bit_select);
    }
  }
  return result;
}

// This is a a very large function and probably should be split into
// smaller chunks.
UHDM::any *CompileHelper::compileExpression(
    DesignComponent *component, const FileContent *fC, NodeId parent,
    CompileDesign *compileDesign, Reduce reduce, UHDM::any *pexpr,
    ValuedComponentI *instance, bool muteErrors) {
  if (m_checkForLoops) {
    m_stackLevel++;
  }
  FileSystem *const fileSystem = FileSystem::getInstance();
  UHDM::Serializer &s = compileDesign->getSerializer();
  UHDM::any *result = nullptr;
  VObjectType parentType = fC->Type(parent);
  UHDM::VectorOfattribute *attributes = nullptr;
  if (parentType == VObjectType::paAttribute_instance) {
    attributes =
        compileAttributes(component, fC, parent, compileDesign, nullptr);
    while (fC->Type(parent) == VObjectType::paAttribute_instance)
      parent = fC->Sibling(parent);
  }
  parentType = fC->Type(parent);
  NodeId child = fC->Child(parent);
  VObjectType childType = VObjectType::sl_INVALID_;
  if (child) {
    childType = fC->Type(child);
  }
  switch (parentType) {
    case VObjectType::paIntegerAtomType_Byte: {
      result = s.MakeByte_var();
      result->VpiParent(pexpr);
      break;
    }
    case VObjectType::paIntegerAtomType_Int: {
      result = s.MakeInt_var();
      result->VpiParent(pexpr);
      break;
    }
    case VObjectType::paIntegerAtomType_Integer: {
      result = s.MakeInteger_var();
      result->VpiParent(pexpr);
      break;
    }
    case VObjectType::paIntegerAtomType_LongInt: {
      result = s.MakeLong_int_var();
      result->VpiParent(pexpr);
      break;
    }
    case VObjectType::paIntegerAtomType_Shortint: {
      result = s.MakeShort_int_var();
      result->VpiParent(pexpr);
      break;
    }
    case VObjectType::paValue_range: {
      UHDM::operation *list_op = s.MakeOperation();
      fC->populateCoreMembers(parent, parent, list_op);
      list_op->VpiOpType(vpiListOp);
      list_op->VpiParent(pexpr);
      UHDM::VectorOfany *operands = s.MakeAnyVec();
      list_op->Operands(operands);
      NodeId lexpr = child;
      NodeId rexpr = fC->Sibling(lexpr);
      if (expr *op = any_cast<expr *>(
              compileExpression(component, fC, lexpr, compileDesign, reduce,
                                list_op, instance, muteErrors))) {
        operands->push_back(op);
      }
      if (rexpr) {
        if (expr *op = any_cast<expr *>(
                compileExpression(component, fC, rexpr, compileDesign, reduce,
                                  list_op, instance, muteErrors))) {
          operands->push_back(op);
        }
      }
      if (attributes != nullptr) {
        list_op->Attributes(attributes);
        for (auto a : *attributes) a->VpiParent(list_op);
      }
      result = list_op;
      fC->populateCoreMembers(parent, parent, result);
      if (m_checkForLoops) {
        m_stackLevel--;
      }
      return result;
    }
    case VObjectType::paNet_lvalue: {
      UHDM::operation *operation = s.MakeOperation();
      UHDM::VectorOfany *operands = s.MakeAnyVec();
      if (attributes != nullptr) {
        operation->Attributes(attributes);
        for (auto a : *attributes) a->VpiParent(operation);
      }
      result = operation;
      operation->VpiParent(pexpr);
      operation->Operands(operands);
      operation->VpiOpType(vpiConcatOp);
      fC->populateCoreMembers(parent, parent, result);
      NodeId Expression = parent;
      while (Expression) {
        if (UHDM::any *exp = compileExpression(
                component, fC, fC->Child(Expression), compileDesign, reduce,
                operation, instance, muteErrors)) {
          operands->push_back(exp);
        }
        Expression = fC->Sibling(Expression);
      }
      if (m_checkForLoops) {
        m_stackLevel--;
      }
      return result;
    }
    case VObjectType::paConcatenation:
    case VObjectType::paConstant_concatenation: {
      UHDM::operation *operation = s.MakeOperation();
      UHDM::VectorOfany *operands = s.MakeAnyVec();
      if (attributes != nullptr) {
        operation->Attributes(attributes);
        for (auto a : *attributes) a->VpiParent(operation);
      }
      result = operation;
      operation->VpiParent(pexpr);
      operation->Operands(operands);
      operation->VpiOpType(vpiConcatOp);
      fC->populateCoreMembers(parent, parent, result);
      NodeId Expression = fC->Child(parent);
      while (Expression) {
        UHDM::any *exp =
            compileExpression(component, fC, Expression, compileDesign, reduce,
                              operation, instance, muteErrors);
        if (exp) operands->push_back(exp);
        Expression = fC->Sibling(Expression);
      }
      child = InvalidNodeId;  // Use parent for location info computation down
                              // below!
      break;
    }
    case VObjectType::paDelay2:
    case VObjectType::paDelay3: {
      NodeId MinTypMax = child;
      if (fC->Sibling(MinTypMax)) {
        UHDM::operation *operation = s.MakeOperation();
        UHDM::VectorOfany *operands = s.MakeAnyVec();
        operation->Operands(operands);
        operation->VpiOpType(vpiListOp);
        operation->VpiParent(pexpr);
        fC->populateCoreMembers(parent, parent, operation);
        result = operation;
        NodeId Expression = MinTypMax;
        while (Expression) {
          UHDM::any *exp =
              compileExpression(component, fC, Expression, compileDesign,
                                reduce, operation, instance, muteErrors);
          if (exp) operands->push_back(exp);
          Expression = fC->Sibling(Expression);
        }
        if (m_checkForLoops) {
          m_stackLevel--;
        }
        return result;
      }
      break;
    }
    case VObjectType::paConstant_mintypmax_expression:
    case VObjectType::paMintypmax_expression: {
      NodeId Expression = child;
      operation *op = s.MakeOperation();
      op->VpiOpType(vpiMinTypMaxOp);
      op->VpiParent(pexpr);
      fC->populateCoreMembers(parent, parent, op);
      UHDM::VectorOfany *operands = s.MakeAnyVec();
      op->Operands(operands);
      result = op;
      while (Expression) {
        expr *sExpr =
            (expr *)compileExpression(component, fC, Expression, compileDesign,
                                      reduce, op, instance, muteErrors);
        if (sExpr) operands->push_back(sExpr);
        Expression = fC->Sibling(Expression);
      }
      if (m_checkForLoops) {
        m_stackLevel--;
      }
      return result;
    }
    case VObjectType::paExpression: {
      NodeId Iff = fC->Sibling(parent);
      if (fC->Type(Iff) == VObjectType::paIFF) {
        operation *op = s.MakeOperation();
        op->VpiOpType(vpiIffOp);
        op->VpiParent(pexpr);
        fC->populateCoreMembers(parent, parent, op);
        UHDM::VectorOfany *operands = s.MakeAnyVec();
        op->Operands(operands);
        result = op;
        expr *lExpr =
            (expr *)compileExpression(component, fC, child, compileDesign,
                                      reduce, op, instance, muteErrors);
        if (lExpr) operands->push_back(lExpr);
        NodeId Expr = fC->Sibling(Iff);
        expr *rExpr =
            (expr *)compileExpression(component, fC, Expr, compileDesign,
                                      reduce, op, instance, muteErrors);
        if (rExpr) operands->push_back(rExpr);
        if (m_checkForLoops) {
          m_stackLevel--;
        }
        return result;
      }
      break;
    }
    case VObjectType::paClass_new: {
      UHDM::method_func_call *sys = s.MakeMethod_func_call();
      sys->VpiName("new");
      sys->VpiParent(pexpr);
      NodeId argListNode = child;
      UHDM::VectorOfany *arguments =
          compileTfCallArguments(component, fC, argListNode, compileDesign,
                                 reduce, sys, instance, muteErrors);
      sys->Tf_call_args(arguments);
      result = sys;
      if (m_checkForLoops) {
        m_stackLevel--;
      }
      return result;
    }
    case VObjectType::paPort_expression: {
      operation *op = s.MakeOperation();
      op->VpiParent(pexpr);
      op->VpiOpType(vpiConcatOp);
      op->Operands(s.MakeAnyVec());
      fC->populateCoreMembers(parent, parent, op);
      auto ops = op->Operands();
      result = op;
      NodeId Port_reference = child;
      while (Port_reference) {
        NodeId Name = fC->Child(Port_reference);
        NodeId Constant_select = fC->Sibling(Name);

        if (fC->Type(Constant_select) == VObjectType::paConstant_select) {
          Constant_select = fC->Child(Constant_select);
        }
        if (fC->Child(Constant_select) || fC->Sibling(Constant_select)) {
          if (any *select = compileSelectExpression(
                  component, fC, Constant_select, "", compileDesign, reduce, op,
                  instance, muteErrors)) {
            ops->push_back(select);
          }
        } else {
          ref_obj *ref = s.MakeRef_obj();
          ops->push_back(ref);
          const std::string_view name = fC->SymName(Name);
          ref->VpiName(name);
          ref->VpiParent(op);
          fC->populateCoreMembers(Port_reference, Port_reference, ref);
          if (pexpr) {
            if (UHDM::any *var =
                    bindVariable(component, pexpr, name, compileDesign))
              ref->Actual_group(var);
            else if (component)
              component->needLateBinding(ref);
          } else if (instance) {
            if (UHDM::any *var =
                    bindVariable(component, instance, name, compileDesign))
              ref->Actual_group(var);
            else if (component)
              component->needLateBinding(ref);
          } else if (component) {
            component->needLateBinding(ref);
          }
        }
        unsupported_typespec *tps = s.MakeUnsupported_typespec();
        if (op->Typespec() == nullptr) {
          ref_typespec *rttps = s.MakeRef_typespec();
          rttps->VpiParent(op);
          op->Typespec(rttps);
        }
        op->Typespec()->Actual_typespec(tps);
        component->needLateTypedefBinding(op);
        Port_reference = fC->Sibling(Port_reference);
      }
      break;
    }
    default:
      break;
  }

  if ((parentType == VObjectType::paVariable_lvalue) &&
      (childType == VObjectType::paVariable_lvalue)) {
    UHDM::operation *operation = s.MakeOperation();
    UHDM::VectorOfany *operands = s.MakeAnyVec();
    if (attributes != nullptr) {
      operation->Attributes(attributes);
      for (auto a : *attributes) a->VpiParent(operation);
    }
    result = operation;
    operation->VpiParent(pexpr);
    operation->Operands(operands);
    operation->VpiOpType(vpiConcatOp);
    fC->populateCoreMembers(parent, parent, result);
    NodeId Expression = child;
    while (Expression) {
      NodeId n = fC->Child(Expression);
      if (fC->Type(n) == VObjectType::paVariable_lvalue) {
        n = Expression;
      }
      if (UHDM::any *exp =
              compileExpression(component, fC, n, compileDesign, reduce,
                                operation, instance, muteErrors)) {
        operands->push_back(exp);
      }
      Expression = fC->Sibling(Expression);
    }
    if (m_checkForLoops) {
      m_stackLevel--;
    }
    return result;
  }

  if (result == nullptr) {
    if (child) {
      switch (childType) {
        case VObjectType::paNull_keyword: {
          UHDM::constant *c = s.MakeConstant();
          c->VpiValue("UINT:0");
          c->VpiDecompile("0");
          c->VpiSize(64);
          c->VpiConstType(vpiNullConst);
          result = c;
          break;
        }
        case VObjectType::paDollar_keyword: {
          UHDM::constant *c = s.MakeConstant();
          c->VpiConstType(vpiUnboundedConst);
          c->VpiValue("STRING:$");
          c->VpiDecompile("$");
          c->VpiSize(1);
          result = c;
          break;
        }
        case VObjectType::paThis_keyword:
        case VObjectType::paSuper_keyword:
        case VObjectType::paThis_dot_super: {
          result = compileComplexFuncCall(component, fC, parent, compileDesign,
                                          reduce, pexpr, instance, muteErrors);
          break;
        }
        case VObjectType::paArray_member_label: {
          UHDM::operation *operation = s.MakeOperation();
          UHDM::VectorOfany *operands = s.MakeAnyVec();
          if (attributes != nullptr) {
            operation->Attributes(attributes);
            for (auto a : *attributes) a->VpiParent(operation);
          }
          result = operation;
          operation->VpiParent(pexpr);
          operation->Operands(operands);
          operation->VpiOpType(vpiConcatOp);
          fC->populateCoreMembers(parent, parent, result);
          NodeId Expression = child;
          bool odd = true;
          while (Expression) {
            NodeId the_exp = fC->Child(Expression);
            if (!the_exp) {
              ref_obj *ref = s.MakeRef_obj();
              ref->VpiName("default");
              operands->push_back(ref);
              ref->VpiParent(operation);
              ref->VpiStructMember(true);
            } else {
              if (UHDM::any *exp = compileExpression(
                      component, fC, the_exp, compileDesign, reduce, operation,
                      instance, muteErrors)) {
                operands->push_back(exp);
                if (odd && (exp->UhdmType() == uhdmref_obj)) {
                  ((ref_obj *)exp)->VpiStructMember(true);
                }
              }
            }
            Expression = fC->Sibling(Expression);
            odd = !odd;
          }
          if (m_checkForLoops) {
            m_stackLevel--;
          }
          return result;
        }
        case VObjectType::paIncDec_PlusPlus:
        case VObjectType::paIncDec_MinusMinus:
        case VObjectType::paUnary_Minus:
        case VObjectType::paUnary_Plus:
        case VObjectType::paUnary_Tilda:
        case VObjectType::paUnary_Not:
        case VObjectType::paNOT:
        case VObjectType::paUnary_BitwOr:
        case VObjectType::paUnary_BitwAnd:
        case VObjectType::paUnary_BitwXor:
        case VObjectType::paUnary_ReductNand:
        case VObjectType::paUnary_ReductNor:
        case VObjectType::paUnary_ReductXnor1:
        case VObjectType::paUnary_ReductXnor2: {
          uint32_t vopType = UhdmWriter::getVpiOpType(childType);
          // This is the PREFIX (pre-increment/pre-decrement) case:
          // operator comes before operand. Map to vpiPreIncOp/vpiPreDecOp.
          if (vopType == vpiPostIncOp) vopType = vpiPreIncOp;
          else if (vopType == vpiPostDecOp) vopType = vpiPreDecOp;
          if (vopType) {
            UHDM::operation *op = s.MakeOperation();
            op->VpiOpType(vopType);
            op->VpiParent(pexpr);
            if (attributes != nullptr) {
              op->Attributes(attributes);
              for (auto a : *attributes) a->VpiParent(op);
            }
            fC->populateCoreMembers(parent, parent, op);
            UHDM::VectorOfany *operands = s.MakeAnyVec();
            NodeId var = fC->Sibling(child);
            if (fC->Type(var) == VObjectType::paVariable_lvalue) {
              var = fC->Child(var);
            }
            if (UHDM::any *operand =
                    compileExpression(component, fC, var, compileDesign, reduce,
                                      op, instance, muteErrors)) {
              operands->push_back(operand);
            }
            op->Operands(operands);
            fC->populateCoreMembers(parent, parent, op);
            result = op;
          }
          break;
        }
        case VObjectType::paEdge_Posedge: {
          UHDM::operation *op = s.MakeOperation();
          op->VpiOpType(vpiPosedgeOp);
          op->VpiParent(pexpr);
          if (attributes != nullptr) {
            op->Attributes(attributes);
            for (auto a : *attributes) a->VpiParent(op);
          }
          if (UHDM::any *operand = compileExpression(
                  component, fC, fC->Sibling(child), compileDesign, reduce, op,
                  instance, muteErrors)) {
            UHDM::VectorOfany *operands = s.MakeAnyVec();
            operands->push_back(operand);
            op->Operands(operands);
            fC->populateCoreMembers(parent, parent, op);
          }
          result = op;
          break;
        }
        case VObjectType::paEdge_Edge: {
          UHDM::operation *op = s.MakeOperation();
          op->VpiOpType(vpiAnyEdge);
          op->VpiParent(pexpr);
          if (attributes != nullptr) {
            op->Attributes(attributes);
            for (auto a : *attributes) a->VpiParent(op);
          }
          if (UHDM::any *operand = compileExpression(
                  component, fC, fC->Sibling(child), compileDesign, reduce, op,
                  instance, muteErrors)) {
            UHDM::VectorOfany *operands = s.MakeAnyVec();
            operands->push_back(operand);
            op->Operands(operands);
            fC->populateCoreMembers(parent, parent, op);
          }
          result = op;
          break;
        }
        case VObjectType::paEdge_Negedge: {
          UHDM::operation *op = s.MakeOperation();
          op->VpiOpType(vpiNegedgeOp);
          op->VpiParent(pexpr);
          if (attributes != nullptr) {
            op->Attributes(attributes);
            for (auto a : *attributes) a->VpiParent(op);
          }
          if (UHDM::any *operand = compileExpression(
                  component, fC, fC->Sibling(child), compileDesign, reduce, op,
                  instance, muteErrors)) {
            UHDM::VectorOfany *operands = s.MakeAnyVec();
            operands->push_back(operand);
            op->Operands(operands);
            fC->populateCoreMembers(parent, parent, op);
          }
          result = op;
          break;
        }
        case VObjectType::paImplicit_class_handle:
        case VObjectType::paInc_or_dec_expression:
        case VObjectType::paConstant_primary:
        case VObjectType::paPrimary_literal:
        case VObjectType::paPrimary:
        case VObjectType::paSystem_task:
        case VObjectType::paParam_expression:
        case VObjectType::paExpression_or_cond_pattern:
        case VObjectType::paConstant_param_expression:
        case VObjectType::paAssignment_pattern_expression:
        case VObjectType::paConstant_assignment_pattern_expression:
        case VObjectType::paConst_or_range_expression:
          result = compileExpression(component, fC, child, compileDesign,
                                     reduce, pexpr, instance, muteErrors);
          break;
        case VObjectType::paExpression_or_dist: {
          result = compileExpression(component, fC, child, compileDesign,
                                     reduce, pexpr, instance, muteErrors);
          if (NodeId dist = fC->Sibling(child)) {
            operation *op = s.MakeOperation();
            op->VpiParent(pexpr);
            fC->populateCoreMembers(parent, parent, op);
            UHDM::VectorOfany *operands = s.MakeAnyVec();
            op->Operands(operands);
            operands->push_back(result);
            VObjectType distType = fC->Type(dist);
            if (distType == VObjectType::paBoolean_abbrev) {
              NodeId repetition = fC->Child(dist);
              VObjectType repetType = fC->Type(repetition);
              op->VpiOpType(UhdmWriter::getVpiOpType(repetType));
              if ((repetType == VObjectType::paConsecutive_repetition) &&
                  (fC->Child(repetition) == InvalidNodeId)) {
              } else {
                if (any *rep = compileExpression(component, fC, repetition,
                                                 compileDesign, reduce, op,
                                                 instance, muteErrors)) {
                  operands->push_back(rep);
                }
              }
              result = op;
            } else if (distType == VObjectType::paTHROUGHOUT ||
                       distType == VObjectType::paWITHIN ||
                       distType == VObjectType::paINTERSECT) {
              NodeId repetition = fC->Sibling(dist);
              op->VpiOpType(UhdmWriter::getVpiOpType(distType));
              if (any *rep = compileExpression(component, fC, repetition,
                                               compileDesign, reduce, op,
                                               instance, muteErrors)) {
                operands->push_back(rep);
              }
              result = op;
            }
          }
          break;
        }
        case VObjectType::paComplex_func_call: {
          result = compileComplexFuncCall(component, fC, fC->Child(child),
                                          compileDesign, reduce, pexpr,
                                          instance, muteErrors);
          break;
        }
        case VObjectType::paDOT: {
          NodeId Identifier = fC->Sibling(child);
          ref_obj *ref = s.MakeRef_obj();
          ref->VpiName(fC->SymName(Identifier));
          ref->VpiParent(pexpr);
          fC->populateCoreMembers(Identifier, Identifier, ref);
          result = ref;
          break;
        }
        case VObjectType::paConstant_mintypmax_expression:
        case VObjectType::paMintypmax_expression: {
          NodeId Expression = fC->Child(child);
          NodeId Sibling = fC->Sibling(Expression);
          if (!Sibling) {
            NodeId Constant_primary = fC->Child(Expression);
            NodeId Constant_expression = fC->Child(Constant_primary);
            NodeId TmpSibling = fC->Sibling(Constant_expression);
            if (TmpSibling &&
                (fC->Type(TmpSibling) == VObjectType::paConstant_expression)) {
              Sibling = TmpSibling;
              Expression = Constant_primary;
            }
          }
          if (Sibling) {
            operation *op = s.MakeOperation();
            op->VpiOpType(vpiMinTypMaxOp);
            op->VpiParent(pexpr);
            fC->populateCoreMembers(parent, parent, op);
            UHDM::VectorOfany *operands = s.MakeAnyVec();
            op->Operands(operands);
            result = op;
            if (expr *cExpr = (expr *)compileExpression(
                    component, fC, Expression, compileDesign, reduce, op,
                    instance, muteErrors)) {
              operands->push_back(cExpr);
            }
            while (Sibling) {
              if (expr *sExpr = (expr *)compileExpression(
                      component, fC, Sibling, compileDesign, reduce, op,
                      instance, muteErrors)) {
                operands->push_back(sExpr);
              }
              Sibling = fC->Sibling(Sibling);
            }
          } else {
            result = (expr *)compileExpression(component, fC, Expression,
                                               compileDesign, reduce, pexpr,
                                               instance, muteErrors);
          }
          break;
        }
        case VObjectType::paRandomize_call: {
          result = compileRandomizeCall(component, fC, fC->Child(child),
                                        compileDesign, pexpr);
          break;
        }
        case VObjectType::paPattern: {
          NodeId Sibling = fC->Sibling(child);
          if (Sibling) {
            operation *op = s.MakeOperation();
            op->VpiOpType(vpiListOp);
            op->VpiParent(pexpr);
            fC->populateCoreMembers(parent, parent, op);
            UHDM::VectorOfany *operands = s.MakeAnyVec();
            op->Operands(operands);
            result = op;
            if (expr *cExpr = (expr *)compileExpression(
                    component, fC, fC->Child(child), compileDesign, reduce, op,
                    instance, muteErrors)) {
              operands->push_back(cExpr);
            }
            while (Sibling) {
              if (expr *sExpr = (expr *)compileExpression(
                      component, fC, Sibling, compileDesign, reduce, op,
                      instance, muteErrors)) {
                operands->push_back(sExpr);
              }
              Sibling = fC->Sibling(Sibling);
            }
          } else {
            result = (expr *)compileExpression(component, fC, fC->Child(child),
                                               compileDesign, reduce, pexpr,
                                               instance, muteErrors);
          }
          break;
        }
        case VObjectType::paTAGGED: {
          NodeId Identifier = fC->Sibling(child);
          NodeId Expression = fC->Sibling(Identifier);
          UHDM::tagged_pattern *pattern = s.MakeTagged_pattern();
          pattern->VpiName(fC->SymName(Identifier));
          pattern->VpiParent(pexpr);
          fC->populateCoreMembers(child, child, pattern);
          if (Expression) {
            pattern->Pattern(compileExpression(component, fC, Expression,
                                               compileDesign, reduce, pattern,
                                               instance, muteErrors));
          }
          result = pattern;
          break;
        }
        case VObjectType::paEvent_expression: {
          NodeId subExpr = child;
          UHDM::any *opL =
              compileExpression(component, fC, subExpr, compileDesign, reduce,
                                pexpr, instance, muteErrors);
          result = opL;
          NodeId op = fC->Sibling(subExpr);
          UHDM::operation *operation = nullptr;
          UHDM::VectorOfany *operands = nullptr;
          while (op) {
            if (operation == nullptr) {
              operation = s.MakeOperation();
              operation->VpiParent(pexpr);
              if (attributes != nullptr) {
                operation->Attributes(attributes);
                for (auto a : *attributes) a->VpiParent(operation);
              }
              operands = s.MakeAnyVec();
              operation->Operands(operands);
              operands->push_back(opL);
              opL->VpiParent(operation);
              result = operation;
            }
            if (fC->Type(op) == VObjectType::paOr_operator) {
              operation->VpiOpType(vpiEventOrOp);
              NodeId subRExpr = fC->Sibling(op);
              if (UHDM::any *opR = compileExpression(
                      component, fC, subRExpr, compileDesign, reduce, operation,
                      instance, muteErrors)) {
                operands->push_back(opR);
              }
              op = fC->Sibling(subRExpr);
            } else if (fC->Type(op) == VObjectType::paComma_operator) {
              operation->VpiOpType(vpiListOp);
              NodeId subRExpr = fC->Sibling(op);
              if (UHDM::any *opR = compileExpression(
                      component, fC, subRExpr, compileDesign, reduce, operation,
                      instance, muteErrors)) {
                operands->push_back(opR);
              }
              op = fC->Sibling(subRExpr);
            }
          }
          if ((operation != nullptr) && (operation->VpiLineNo() == 0)) {
            fC->populateCoreMembers(parent, parent, operation);
          }
          break;
        }
        case VObjectType::paExpression:
        case VObjectType::paConstant_expression: {
          UHDM::any *opL =
              compileExpression(component, fC, child, compileDesign, reduce,
                                pexpr, instance, muteErrors);
          NodeId op = fC->Sibling(child);
          if ((!op) || (fC->Type(op) == VObjectType::paConstant_expression)) {
            result = opL;
            break;
          }
          VObjectType opType = fC->Type(op);
          uint32_t vopType = UhdmWriter::getVpiOpType(opType);
          if (opType == VObjectType::paQMARK ||
              opType == VObjectType::paConditional_operator) {  // Ternary op
            if ((reduce == Reduce::Yes) && (opL->UhdmType() == uhdmconstant)) {
              UHDM::ExprEval eval;
              bool invalidValue = false;
              int64_t cond = eval.get_value(invalidValue, (expr *)opL);
              if (cond) {
                NodeId rval = fC->Sibling(op);
                result = compileExpression(component, fC, rval, compileDesign,
                                           reduce, pexpr, instance, muteErrors);
                break;
              } else {
                NodeId rval = fC->Sibling(op);
                rval = fC->Sibling(rval);
                result = compileExpression(component, fC, rval, compileDesign,
                                           reduce, pexpr, instance, muteErrors);
                break;
              }
            }
          }

          UHDM::operation *operation = s.MakeOperation();
          UHDM::VectorOfany *operands = s.MakeAnyVec();
          result = operation;
          operation->VpiParent(pexpr);
          if (attributes != nullptr) {
            operation->Attributes(attributes);
            for (auto a : *attributes) a->VpiParent(operation);
          }
          fC->populateCoreMembers(parent, parent, operation);
          if (opL) {
            opL->VpiParent(operation);
            operands->push_back(opL);
          }
          if (vopType == 0) {
            result = nullptr;
          }
          operation->VpiOpType(vopType);

          operation->Operands(operands);
          NodeId rval = fC->Sibling(op);

          if (fC->Type(rval) == VObjectType::paAttribute_instance) {
            if (UHDM::VectorOfattribute *attributes = compileAttributes(
                    component, fC, rval, compileDesign, operation)) {
              operation->Attributes(attributes);
              for (auto a : *attributes) a->VpiParent(operation);
            }
            while (fC->Type(rval) == VObjectType::paAttribute_instance)
              rval = fC->Sibling(rval);
          }
          if (opType == VObjectType::paINSIDE) {
            // Because open_range_list is stored in { }, it is being interpreted
            // as a concatenation operation. Code below constructs it manually.
            // Example tree:
            // n<> u<164> t<InsideOp> p<180> s<179> l<9>
            // n<> u<179> t<Expression> p<180> c<178> l<9>
            //    n<> u<178> t<Primary> p<179> c<177> l<9>
            //        n<> u<177> t<Concatenation> p<178> c<168> l<9>
            //            n<> u<168> t<Expression> p<177> c<167> s<172> l<9>
            //                n<> u<167> t<Primary> p<168> c<166> l<9>
            //                    n<> u<166> t<Primary_literal> p<167> c<165>
            //                    l<9>
            //                        n<OP_1> u<165> t<StringConst> p<166> l<9>
            //            n<> u<172> t<Expression> p<177> c<171> s<176> l<10>
            //                n<> u<171> t<Primary> p<172> c<170> l<10>
            //                    n<> u<170> t<Primary_literal> p<171> c<169>
            //                    l<10>
            //                        n<OP_2> u<169> t<StringConst> p<170> l<10>
            //            n<> u<176> t<Expression> p<177> c<175> l<11>
            //                n<> u<175> t<Primary> p<176> c<174> l<11>
            //                    n<> u<174> t<Primary_literal> p<175> c<173>
            //                    l<11>
            //                        n<OP_3> u<173> t<StringConst> p<174> l<11>
            NodeId false_concat = fC->Child(fC->Child(rval));
            NodeId Expression = fC->Child(false_concat);
            // Open range list members
            while (Expression) {
              if (UHDM::any *exp = compileExpression(
                      component, fC, Expression, compileDesign, reduce,
                      operation, instance, muteErrors)) {
                operands->push_back(exp);
              }
              Expression = fC->Sibling(Expression);
            }
            // RHS is done, skip handling below
            break;
          } else if (opType == VObjectType::paOpen_range_list) {
            NodeId Value_range = fC->Child(op);
            NodeId Expression = fC->Child(Value_range);
            while (Expression) {
              if (UHDM::any *exp = compileExpression(
                      component, fC, Expression, compileDesign, reduce,
                      operation, instance, muteErrors)) {
                operands->push_back(exp);
              }
              Expression = fC->Sibling(Expression);
            }
            // RHS is done, skip handling below
            break;
          }

          if (UHDM::any *opR =
                  compileExpression(component, fC, rval, compileDesign, reduce,
                                    operation, instance, muteErrors)) {
            opR->VpiParent(operation);
            operands->push_back(opR);
          }
          if (opType == VObjectType::paQMARK ||
              opType == VObjectType::paConditional_operator) {  // Ternary op
            rval = fC->Sibling(rval);
            if (UHDM::any *opR = compileExpression(
                    component, fC, rval, compileDesign, reduce, operation,
                    instance, muteErrors)) {
              opR->VpiParent(operation);
              operands->push_back(opR);
            }
          }
          fC->populateCoreMembers(child, rval, operation);
          break;
        }
        case VObjectType::paSystem_task_names: {
          // Node example:
          // n<> u<23> t<System_task_names> p<29> c<22> s<28> l<2>
          //     n<$unsigned> u<22> t<StringConst> p<23> l<2>
          // n<> u<28> t<List_of_arguments> p<29> c<27> l<2>
          //     n<> u<27> t<Expression> p<28> c<26> l<2>
          //         n<> u<26> t<Primary> p<27> c<25> l<2>
          //             n<> u<25> t<Primary_literal> p<26> c<24> l<2>
          //                 n<a> u<24> t<StringConst> p<25> l<2>

          NodeId n = fC->Child(child);
          const std::string_view name = fC->SymName(n);
          if (name == "$bits") {
            NodeId List_of_arguments = fC->Sibling(child);
            result =
                compileBits(component, fC, List_of_arguments, compileDesign,
                            reduce, pexpr, instance, false, muteErrors);
          } else if (name == "$size") {
            NodeId List_of_arguments = fC->Sibling(child);
            result =
                compileBits(component, fC, List_of_arguments, compileDesign,
                            reduce, pexpr, instance, true, muteErrors);
          } else if (name == "$high" || name == "$low" || name == "$left" ||
                     name == "$right") {
            NodeId List_of_arguments = fC->Sibling(child);
            result =
                compileBound(component, fC, List_of_arguments, compileDesign,
                             reduce, pexpr, instance, muteErrors, name);
          } else if (name == "$clog2") {
            NodeId List_of_arguments = fC->Sibling(child);
            result =
                compileClog2(component, fC, List_of_arguments, compileDesign,
                             reduce, pexpr, instance, muteErrors);
          } else if (name == "$typename") {
            NodeId List_of_arguments = fC->Sibling(child);
            result = compileTypename(component, fC, List_of_arguments,
                                     compileDesign, reduce, pexpr, instance);
          } else {
            UHDM::sys_func_call *sys = s.MakeSys_func_call();
            sys->VpiName(name);
            sys->VpiParent(pexpr);
            NodeId argListNode = fC->Sibling(child);
            VectorOfany *arguments = compileTfCallArguments(
                component, fC, argListNode, compileDesign, reduce, sys,
                instance, muteErrors);
            sys->Tf_call_args(arguments);
            result = sys;
          }
          break;
        }
        case VObjectType::paVariable_lvalue: {
          UHDM::any *variable =
              compileExpression(component, fC, fC->Child(child), compileDesign,
                                reduce, pexpr, instance, muteErrors);
          NodeId op = fC->Sibling(child);
          if (op) {
            fC->populateCoreMembers(child, child, variable);

            VObjectType opType = fC->Type(op);
            uint32_t vopType = UhdmWriter::getVpiOpType(opType);
            if (vopType) {
              // Post increment/decrement
              UHDM::operation *operation = s.MakeOperation();
              UHDM::VectorOfany *operands = s.MakeAnyVec();
              if (attributes != nullptr) {
                operation->Attributes(attributes);
                for (auto a : *attributes) a->VpiParent(operation);
              }
              fC->populateCoreMembers(parent, parent, operation);
              operation->VpiParent(pexpr);
              operation->VpiOpType(vopType);
              operation->Operands(operands);
              operands->push_back(variable);
              variable->VpiParent(operation);
              result = operation;
              NodeId rval = fC->Sibling(op);
              if (fC->Type(rval) == VObjectType::paAttribute_instance) {
                if (UHDM::VectorOfattribute *attributes = compileAttributes(
                        component, fC, rval, compileDesign, operation)) {
                  operation->Attributes(attributes);
                  for (auto a : *attributes) a->VpiParent(operation);
                }
                while (fC->Type(rval) == VObjectType::paAttribute_instance)
                  rval = fC->Sibling(rval);
              }
            } else if (opType == VObjectType::paExpression) {
              // Assignment
              UHDM::operation *operation = s.MakeOperation();
              UHDM::VectorOfany *operands = s.MakeAnyVec();
              if (attributes != nullptr) {
                operation->Attributes(attributes);
                for (auto a : *attributes) a->VpiParent(operation);
              }
              fC->populateCoreMembers(parent, parent, operation);
              operation->VpiParent(pexpr);
              operation->VpiOpType(vpiAssignmentOp);
              operation->Operands(operands);
              operands->push_back(variable);
              result = operation;

              NodeId rval = op;
              if (fC->Type(rval) == VObjectType::paAttribute_instance) {
                if (UHDM::VectorOfattribute *attributes = compileAttributes(
                        component, fC, rval, compileDesign, operation)) {
                  operation->Attributes(attributes);
                  for (auto a : *attributes) a->VpiParent(operation);
                }
                while (fC->Type(rval) == VObjectType::paAttribute_instance)
                  rval = fC->Sibling(rval);
              }

              if (UHDM::any *rexp = compileExpression(
                      component, fC, rval, compileDesign, reduce, operation,
                      instance, muteErrors)) {
                operands->push_back(rexp);
              }
            }
          } else {
            result = variable;
          }
          break;
        }
        case VObjectType::paAssignment_pattern: {
          result = compileAssignmentPattern(component, fC, child, compileDesign,
                                            reduce, pexpr, instance);
          break;
        }
        case VObjectType::paSequence_instance: {
          NodeId Ps_or_hierarchical_sequence_identifier = fC->Child(child);
          NodeId Ps_or_hierarchical_array_identifier =
              fC->Child(Ps_or_hierarchical_sequence_identifier);
          NodeId NameId = fC->Child(Ps_or_hierarchical_array_identifier);
          const std::string_view name = fC->SymName(NameId);
          sequence_inst *seqinst = s.MakeSequence_inst();
          fC->populateCoreMembers(child, child, seqinst);
          seqinst->VpiName(name);
          seqinst->VpiParent(pexpr);
          NodeId Sequence_list_of_arguments =
              fC->Sibling(Ps_or_hierarchical_sequence_identifier);
          NodeId Sequence_actual_arg = fC->Child(Sequence_list_of_arguments);
          VectorOfany *args = s.MakeAnyVec();
          seqinst->Named_event_sequence_expr_groups(args);
          while (Sequence_actual_arg) {
            NodeId arg = Sequence_actual_arg;
            if (fC->Type(Sequence_actual_arg) == VObjectType::paSequence_arg) {
              arg = fC->Child(Sequence_actual_arg);
            }
            if (arg) {
              NodeId Event_expression = fC->Child(arg);
              if (any *exp = compileExpression(component, fC, Event_expression,
                                               compileDesign, reduce, seqinst,
                                               instance, muteErrors)) {
                args->push_back(exp);
              }
            } else {
              constant *c = s.MakeConstant();
              c->VpiValue("INT:0");
              c->VpiDecompile("0");
              c->VpiSize(64);
              c->VpiConstType(vpiIntConst);
              fC->populateCoreMembers(Sequence_actual_arg, Sequence_actual_arg,
                                      c);
              args->push_back(c);
            }
            Sequence_actual_arg = fC->Sibling(Sequence_actual_arg);
          }
          result = seqinst;
          break;
        }
        case VObjectType::paSequence_expr: {
          result = compileExpression(component, fC, child, compileDesign,
                                     reduce, pexpr, instance, muteErrors);
          if (NodeId oper = fC->Sibling(child)) {
            VObjectType type = fC->Type(oper);
            operation *operation = s.MakeOperation();
            operation->VpiParent(pexpr);
            UHDM::VectorOfany *operands = s.MakeAnyVec();
            operation->Operands(operands);
            result->VpiParent(operation);
            operands->push_back(result);
            fC->populateCoreMembers(parent, parent, operation);
            int32_t operationType = UhdmWriter::getVpiOpType(type);
            if (NodeId subOp1 = fC->Child(oper)) {
              VObjectType subOp1type = fC->Type(subOp1);
              if (subOp1type == VObjectType::paPound_Pound_delay) {
                if (NodeId subOp2 = fC->Sibling(subOp1)) {
                  VObjectType subOp2type = fC->Type(subOp2);
                  if (subOp2type == VObjectType::paAssociative_dimension) {
                    operationType = vpiConsecutiveRepeatOp;
                  } else if (subOp2type ==
                             VObjectType::
                                 paCycle_delay_const_range_expression) {
                    UHDM::range *r = s.MakeRange();
                    NodeId lhs = fC->Child(subOp2);
                    NodeId rhs = fC->Sibling(lhs);
                    r->Left_expr((expr *)compileExpression(
                        component, fC, lhs, compileDesign, reduce, r, instance,
                        muteErrors));
                    r->Right_expr((expr *)compileExpression(
                        component, fC, rhs, compileDesign, reduce, r, instance,
                        muteErrors));
                    fC->populateCoreMembers(subOp2, subOp2, r);
                    operands->push_back(r);
                  }
                } else {
                  std::string_view val = fC->SymName(subOp1);
                  val.remove_prefix(2);
                  UHDM::constant *c = s.MakeConstant();
                  c->VpiValue(StrCat("UINT:", val));
                  c->VpiDecompile(val);
                  c->VpiSize(64);
                  c->VpiConstType(vpiUIntConst);
                  fC->populateCoreMembers(subOp1, subOp1, c);
                  operands->push_back(c);
                }
              }
            }
            operation->VpiOpType(operationType);
            if (any *rhs = compileExpression(component, fC, fC->Sibling(oper),
                                             compileDesign, reduce, operation,
                                             instance, muteErrors)) {
              operands->push_back(rhs);
            }
            result = operation;
          }
          break;
        }
        case VObjectType::paConstant_cast:
        case VObjectType::paCast: {
          NodeId Casting_type = fC->Child(child);
          NodeId Simple_type = fC->Child(Casting_type);
          UHDM::any *operand = nullptr;
          if (Casting_type) {
            NodeId Expression = fC->Sibling(Casting_type);
            operand =
                compileExpression(component, fC, Expression, compileDesign,
                                  reduce, nullptr, instance, muteErrors);
          }
          if ((fC->Type(Simple_type) == VObjectType::paSigning_Unsigned) ||
              (fC->Type(Simple_type) == VObjectType::paSigning_Signed)) {
            UHDM::sys_func_call *sys = s.MakeSys_func_call();
            if (fC->Type(Simple_type) == VObjectType::paSigning_Unsigned)
              sys->VpiName("$unsigned");
            else
              sys->VpiName("$signed");
            sys->VpiParent(pexpr);
            VectorOfany *arguments = s.MakeAnyVec();
            sys->Tf_call_args(arguments);
            if (operand) {
              arguments->push_back(operand);
              operand->VpiParent(sys);
            }
            result = sys;
          } else {
            UHDM::operation *operation = s.MakeOperation();
            UHDM::VectorOfany *operands = s.MakeAnyVec();
            if (attributes != nullptr) {
              operation->Attributes(attributes);
              for (auto a : *attributes) a->VpiParent(operation);
            }
            operation->Operands(operands);
            operation->VpiOpType(vpiCastOp);
            operation->VpiParent(pexpr);
            fC->populateCoreMembers(parent, parent, operation);
            if (operand) {
              operands->push_back(operand);
              operand->VpiParent(operation);
            }
            if (UHDM::typespec *tps =
                    compileTypespec(component, fC, Simple_type, compileDesign,
                                    reduce, operation, instance, false)) {
              if (operation->Typespec() == nullptr) {
                ref_typespec *rttps = s.MakeRef_typespec();
                rttps->VpiParent(operation);
                operation->Typespec(rttps);
              }
              operation->Typespec()->Actual_typespec(tps);
              if (tps->UhdmType() == uhdmunsupported_typespec) {
                component->needLateTypedefBinding(operation);
              }
            }
            result = operation;
          }
          break;
        }
        case VObjectType::paPackage_scope:
        case VObjectType::paClass_type:
        case VObjectType::paHierarchical_identifier:
        case VObjectType::slStringConst: {
          std::string name;
          Value *sval = nullptr;
          if (childType == VObjectType::paPackage_scope) {
            const std::string_view packageName = fC->SymName(fC->Child(child));
            NodeId paramId = fC->Sibling(child);
            NodeId selectId = fC->Sibling(paramId);
            const std::string_view n = fC->SymName(paramId);
            name.assign(packageName).append("::").append(n);
            if (m_elabMode) {
              Package *pack =
                  compileDesign->getCompiler()->getDesign()->getPackage(
                      packageName);
              if (pack) {
                UHDM::VectorOfparam_assign *param_assigns =
                    pack->getParam_assigns();
                if (param_assigns) {
                  for (param_assign *param : *param_assigns) {
                    if (param && param->Lhs()) {
                      const std::string_view param_name =
                          param->Lhs()->VpiName();
                      if (param_name == n) {
                        if (substituteAssignedValue(param->Rhs(),
                                                    compileDesign)) {
                          ElaboratorContext elaboratorContext(&s, false, true);
                          result = UHDM::clone_tree(param->Rhs(),
                                                    &elaboratorContext);
                          result->VpiParent(pexpr);
                          fC->populateCoreMembers(child, child, result);
                        }
                        break;
                      }
                    }
                  }
                }
                if (result && selectId) {
                  if (fC->Type(selectId) == VObjectType::paConstant_select) {
                    selectId = fC->Child(selectId);
                  }
                  if (fC->Child(selectId) || fC->Sibling(selectId))
                    result = compileSelectExpression(
                        component, fC, selectId, name, compileDesign, reduce,
                        pexpr, instance, muteErrors);
                }
                if (result == nullptr) sval = pack->getValue(n);
              }
            } else {
              // create ref_obj down below
            }
          } else if (childType == VObjectType::paClass_type) {
            const std::string_view packageName = fC->SymName(fC->Child(child));
            name = packageName;
            std::string n;
            if (fC->Sibling(parent)) {
              n = fC->SymName(fC->Sibling(parent));
              name += "::" + n;
            }
            Package *pack =
                compileDesign->getCompiler()->getDesign()->getPackage(
                    packageName);
            if (m_elabMode) {
              if (pack) {
                UHDM::VectorOfparam_assign *param_assigns =
                    pack->getParam_assigns();
                if (param_assigns) {
                  for (param_assign *param : *param_assigns) {
                    if (param && param->Lhs()) {
                      const std::string_view param_name =
                          param->Lhs()->VpiName();
                      if (param_name == n) {
                        if (substituteAssignedValue(param->Rhs(),
                                                    compileDesign)) {
                          ElaboratorContext elaboratorContext(&s, false, true);
                          result = UHDM::clone_tree(param->Rhs(),
                                                    &elaboratorContext);
                          fC->populateCoreMembers(child, child, result);
                        }
                        break;
                      }
                    }
                  }
                }
                if (result == nullptr) sval = pack->getValue(n);
              }
            } else {
              // create ref_obj down below
            }
          } else {
            NodeId rhs;
            if (parentType == VObjectType::paHierarchical_identifier ||
                parentType == VObjectType::paPs_or_hierarchical_identifier) {
              rhs = parent;
            } else {
              rhs = child;
            }
            if (fC->Name(child))
              name = fC->SymName(child);
            else {
              NodeId tmp = fC->Child(child);
              if (fC->Type(tmp) == VObjectType::paDollar_root_keyword) {
                tmp = fC->Sibling(tmp);
              }
              name = fC->SymName(tmp);
            }
            NodeId rhsbackup = rhs;
            while ((rhs = fC->Sibling(rhs))) {
              VObjectType type = fC->Type(rhs);
              if (type == VObjectType::slStringConst) {
                if (fC->Type(rhsbackup) == VObjectType::paPackage_scope) {
                  name.append("::").append(fC->SymName(rhs));
                } else {
                  name.append(".").append(fC->SymName(rhs));
                }
              } else if (type == VObjectType::paSelect ||
                         type == VObjectType::paConstant_select) {
                NodeId Bit_select = fC->Child(rhs);
                result = compileSelectExpression(component, fC, Bit_select,
                                                 name, compileDesign, reduce,
                                                 pexpr, instance, muteErrors);
                if (result != nullptr) {
                  fC->populateCoreMembers(rhsbackup, rhs, result);
                }
              } else if (type == VObjectType::paIncDec_PlusPlus ||
                         type == VObjectType::paIncDec_MinusMinus) {
                uint32_t vopType = UhdmWriter::getVpiOpType(type);
                if (vopType) {
                  UHDM::operation *op = s.MakeOperation();
                  op->Attributes(attributes);
                  op->VpiOpType(vopType);
                  op->VpiParent(pexpr);
                  UHDM::VectorOfany *operands = s.MakeAnyVec();
                  UHDM::ref_obj *ref = s.MakeRef_obj();
                  ref->VpiName(name);
                  ref->VpiParent(pexpr);
                  if (pexpr) {
                    if (UHDM::any *var =
                            bindVariable(component, pexpr, name, compileDesign))
                      ref->Actual_group(var);
                    else if (component)
                      component->needLateBinding(ref);
                  } else if (instance) {
                    if (UHDM::any *var = bindVariable(component, instance, name,
                                                      compileDesign))
                      ref->Actual_group(var);
                    else if (component)
                      component->needLateBinding(ref);
                  } else if (component) {
                    component->needLateBinding(ref);
                  }
                  operands->push_back(ref);
                  op->Operands(operands);
                  result = op;
                }
              }
              if (result) break;
            }
            if (result) break;
            if ((reduce == Reduce::Yes) && instance)
              sval = instance->getValue(name);
          }
          if (result) break;

          if (sval == nullptr || (sval && !sval->isValid())) {
            expr *complexValue = nullptr;
            if (instance) {
              if (ModuleInstance *inst =
                      valuedcomponenti_cast<ModuleInstance *>(instance)) {
                if (Netlist *netlist = inst->getNetlist()) {
                  if (UHDM::VectorOfparam_assign *param_assigns =
                          netlist->param_assigns()) {
                    for (param_assign *param_ass : *param_assigns) {
                      if (param_ass && param_ass->Lhs()) {
                        const std::string_view param_name =
                            param_ass->Lhs()->VpiName();
                        if (param_name == name) {
                          if ((reduce == Reduce::Yes) ||
                              (param_ass->Rhs() &&
                               (param_ass->Rhs()->UhdmType() ==
                                uhdmconstant))) {
                            if (substituteAssignedValue(param_ass->Rhs(),
                                                        compileDesign)) {
                              ElaboratorContext elaboratorContext(&s, false,
                                                                  true);
                              result = UHDM::clone_tree(param_ass->Rhs(),
                                                        &elaboratorContext);
                              result->VpiParent(param_ass);
                              fC->populateCoreMembers(child, child, result);
                              typespec *tps = nullptr;
                              const any *lhs = param_ass->Lhs();
                              if (lhs->UhdmType() == UHDM::uhdmtype_parameter) {
                                if (ref_typespec *lhs_rt =
                                        ((UHDM::type_parameter *)lhs)
                                            ->Typespec()) {
                                  tps = lhs_rt->Actual_typespec();
                                }
                              } else if (lhs->UhdmType() ==
                                         UHDM::uhdmparameter) {
                                if (ref_typespec *lhs_rt =
                                        ((UHDM::parameter *)lhs)->Typespec()) {
                                  tps = lhs_rt->Actual_typespec();
                                }
                              }
                              expr *res = (expr *)result;
                              if (tps && (res->Typespec() == nullptr)) {
                                ref_typespec *tps_rt = s.MakeRef_typespec();
                                tps_rt->VpiParent(res);
                                tps_rt->Actual_typespec(tps);
                                res->Typespec(tps_rt);
                              }
                              break;
                            }
                          }
                        }
                      }
                    }
                  }
                }
                if (expr *complex = inst->getComplexValue(name)) {
                  complexValue = complex;
                }
              }
            }
            if (component && (result == nullptr)) {
              if (UHDM::VectorOfparam_assign *param_assigns =
                      component->getParam_assigns()) {
                for (param_assign *param_ass : *param_assigns) {
                  if (param_ass && param_ass->Lhs()) {
                    const std::string_view param_name =
                        param_ass->Lhs()->VpiName();
                    bool paramFromPackage = false;
                    if ((valuedcomponenti_cast<Package *>(component)) &&
                        (reduce == Reduce::Yes)) {
                      paramFromPackage = true;
                    }
                    if (param_ass->Lhs()->UhdmType() == uhdmparameter) {
                      const parameter *tp = (parameter *)param_ass->Lhs();
                      if (!tp->VpiImported().empty()) {
                        paramFromPackage = true;
                      }
                    }
                    if (param_name == name) {
                      if ((reduce == Reduce::Yes) ||
                          (paramFromPackage &&
                           (param_ass->Rhs()->UhdmType() == uhdmconstant))) {
                        if (substituteAssignedValue(param_ass->Rhs(),
                                                    compileDesign)) {
                          if (complexValue) {
                            result = complexValue;
                          } else {
                            ElaboratorContext elaboratorContext(&s, false,
                                                                true);
                            result = UHDM::clone_tree(param_ass->Rhs(),
                                                      &elaboratorContext);
                            result->VpiParent(param_ass);
                            fC->populateCoreMembers(child, child, result);
                          }
                          typespec *tps = nullptr;
                          const any *lhs = param_ass->Lhs();
                          if (lhs->UhdmType() == UHDM::uhdmtype_parameter) {
                            if (ref_typespec *lhs_rt =
                                    ((UHDM::type_parameter *)lhs)->Typespec()) {
                              tps = lhs_rt->Actual_typespec();
                            }
                          } else if (lhs->UhdmType() == UHDM::uhdmparameter) {
                            if (ref_typespec *lhs_rt =
                                    ((UHDM::parameter *)lhs)->Typespec()) {
                              tps = lhs_rt->Actual_typespec();
                            }
                          }

                          expr *res = (expr *)result;
                          if (tps && (res->Typespec() == nullptr)) {
                            ref_typespec *tps_rt = s.MakeRef_typespec();
                            tps_rt->VpiParent(res);
                            tps_rt->Actual_typespec(tps);
                            res->Typespec(tps_rt);
                          }
                          break;
                        }
                      }
                    }
                  }
                }
              }
            }
            if (result == nullptr) {
              UHDM::ref_obj *ref = s.MakeRef_obj();
              ref->VpiName(name);
              ref->VpiParent(pexpr);
              fC->populateCoreMembers(parent, parent, ref);
              if (pexpr) {
                if (UHDM::any *var =
                        bindVariable(component, pexpr, name, compileDesign))
                  ref->Actual_group(var);
                else if (component)
                  component->needLateBinding(ref);
              } else if (instance) {
                if (UHDM::any *var =
                        bindVariable(component, instance, name, compileDesign))
                  ref->Actual_group(var);
                else if (component)
                  component->needLateBinding(ref);
              } else if (component) {
                component->needLateBinding(ref);
              }
              result = ref;
            }
          } else {
            UHDM::constant *c = s.MakeConstant();
            c->VpiValue(sval->uhdmValue());
            c->VpiDecompile(sval->decompiledValue());
            c->VpiConstType(sval->vpiValType());
            c->VpiSize(sval->getSize());
            if (sval->isSigned()) {
              int_typespec *ts = s.MakeInt_typespec();
              ts->VpiSigned(true);
              ref_typespec *rt = s.MakeRef_typespec();
              rt->VpiParent(c);
              rt->Actual_typespec(ts);
              c->Typespec(rt);
            }
            result = c;
          }
          break;
        }
        case VObjectType::slIntConst:
        case VObjectType::slRealConst:
        case VObjectType::paNumber_1Tickb1:
        case VObjectType::paNumber_1TickB1:
        case VObjectType::paInitVal_1Tickb1:
        case VObjectType::paInitVal_1TickB1:
        case VObjectType::paScalar_1Tickb1:
        case VObjectType::paScalar_1TickB1:
        case VObjectType::pa1:
        case VObjectType::paScalar_Tickb1:
        case VObjectType::paScalar_TickB1:
        case VObjectType::paNumber_Tickb1:
        case VObjectType::paNumber_TickB1:
        case VObjectType::paNumber_Tick1:
        case VObjectType::paNumber_1Tickb0:
        case VObjectType::paNumber_1TickB0:
        case VObjectType::paInitVal_1Tickb0:
        case VObjectType::paInitVal_1TickB0:
        case VObjectType::paScalar_1Tickb0:
        case VObjectType::paScalar_1TickB0:
        case VObjectType::pa0:
        case VObjectType::paScalar_Tickb0:
        case VObjectType::paScalar_TickB0:
        case VObjectType::paNumber_Tickb0:
        case VObjectType::paNumber_TickB0:
        case VObjectType::paNumber_Tick0:
        case VObjectType::paNumber_1TickBX:
        case VObjectType::paNumber_1TickbX:
        case VObjectType::paNumber_1Tickbx:
        case VObjectType::paNumber_1TickBx:
        case VObjectType::paInitVal_1Tickbx:
        case VObjectType::paInitVal_1TickbX:
        case VObjectType::paInitVal_1TickBx:
        case VObjectType::paInitVal_1TickBX:
        case VObjectType::paX:
        case VObjectType::paZ:
        case VObjectType::paTime_literal:
        case VObjectType::slStringLiteral: {
          result = compileConst(fC, child, s);
          break;
        }
        case VObjectType::paStreaming_concatenation: {
          UHDM::operation *operation = s.MakeOperation();
          UHDM::VectorOfany *operands = s.MakeAnyVec();
          if (attributes != nullptr) {
            operation->Attributes(attributes);
            for (auto a : *attributes) a->VpiParent(operation);
          }
          operation->VpiParent(pexpr);
          operation->Operands(operands);
          result = operation;
          NodeId Stream_operator = fC->Child(child);
          NodeId Stream_direction = fC->Child(Stream_operator);
          NodeId Slice_size = fC->Sibling(Stream_operator);
          UHDM::any *exp_slice = nullptr;
          NodeId Stream_concatenation;
          if (fC->Type(Slice_size) == VObjectType::paSlice_size) {
            NodeId Constant_expression = fC->Child(Slice_size);
            if (fC->Type(Constant_expression) == VObjectType::paSimple_type) {
              NodeId Integer_type = fC->Child(Constant_expression);
              NodeId Type = fC->Child(Integer_type);
              exp_slice =
                  compileBits(component, fC, Type, compileDesign, Reduce::Yes,
                              operation, instance, false, muteErrors);
            } else {
              exp_slice = compileExpression(component, fC, Constant_expression,
                                            compileDesign, reduce, operation,
                                            instance, muteErrors);
            }
            Stream_concatenation = fC->Sibling(Slice_size);
          } else {
            Stream_concatenation = Slice_size;
          }

          fC->populateCoreMembers(Stream_concatenation, Stream_concatenation,
                                  operation);
          if (fC->Type(Stream_direction) == VObjectType::paBinOp_ShiftRight)
            operation->VpiOpType(vpiStreamLROp);
          else
            operation->VpiOpType(vpiStreamRLOp);
          if (exp_slice) operands->push_back(exp_slice);

          UHDM::operation *concat_op = s.MakeOperation();
          UHDM::VectorOfany *concat_ops = s.MakeAnyVec();
          operands->push_back(concat_op);
          concat_op->VpiParent(operation);
          concat_op->Operands(concat_ops);
          concat_op->VpiOpType(vpiConcatOp);
          fC->populateCoreMembers(parent, parent, concat_op);

          NodeId Stream_expression = fC->Child(Stream_concatenation);
          while (Stream_expression) {
            NodeId Expression = fC->Child(Stream_expression);
            if (UHDM::any *exp_var = compileExpression(
                    component, fC, Expression, compileDesign, reduce, concat_op,
                    instance, muteErrors)) {
              concat_ops->push_back(exp_var);
            }
            Stream_expression = fC->Sibling(Stream_expression);
          }
          break;
        }
        case VObjectType::paEmpty_queue: {
          UHDM::array_var *var = s.MakeArray_var();
          ref_typespec *rt = s.MakeRef_typespec();
          rt->VpiParent(var);
          rt->Actual_typespec(s.MakeArray_typespec());
          var->Typespec(rt);
          var->VpiArrayType(vpiQueueArray);
          result = var;
          break;
        }
        case VObjectType::paConstant_concatenation:
        case VObjectType::paConcatenation: {
          UHDM::VectorOfany *operands = s.MakeAnyVec();
          NodeId Expression = fC->Child(child);
          UHDM::operation *operation = s.MakeOperation();
          if (attributes != nullptr) {
            operation->Attributes(attributes);
            for (auto a : *attributes) a->VpiParent(operation);
          }
          result = operation;
          while (Expression) {
            if (UHDM::any *exp = compileExpression(
                    component, fC, Expression, compileDesign, reduce, operation,
                    instance, muteErrors)) {
              operands->push_back(exp);
            }
            Expression = fC->Sibling(Expression);
          }
          operation->VpiParent(pexpr);
          operation->Operands(operands);
          operation->VpiOpType(vpiConcatOp);
          fC->populateCoreMembers(parent, parent, operation);
          break;
        }
        case VObjectType::paConstant_multiple_concatenation:
        case VObjectType::paMultiple_concatenation: {
          UHDM::operation *operation = s.MakeOperation();
          UHDM::VectorOfany *operands = s.MakeAnyVec();
          if (attributes != nullptr) {
            operation->Attributes(attributes);
            for (auto a : *attributes) a->VpiParent(operation);
          }
          result = operation;
          operation->VpiParent(pexpr);
          operation->Operands(operands);
          operation->VpiOpType(vpiMultiConcatOp);
          fC->populateCoreMembers(parent, parent, operation);
          NodeId NCopy = fC->Child(child);
          if (UHDM::any *exp =
                  compileExpression(component, fC, NCopy, compileDesign, reduce,
                                    operation, instance, muteErrors)) {
            operands->push_back(exp);
          }
          NodeId Concatenation = fC->Sibling(NCopy);
          if (UHDM::any *exp =
                  compileExpression(component, fC, Concatenation, compileDesign,
                                    reduce, operation, instance, muteErrors)) {
            operands->push_back(exp);
          }
          break;
        }
        case VObjectType::paSubroutine_call: {
          NodeId Dollar_keyword = fC->Child(child);
          NodeId nameId;
          if (fC->Type(Dollar_keyword) == VObjectType::slStringConst) {
            nameId = Dollar_keyword;
          } else {
            nameId = fC->Sibling(Dollar_keyword);
          }
          NodeId List_of_arguments = fC->Sibling(nameId);
          std::string name(fC->SymName(nameId));
          if (name == "bits") {
            NodeId Expression = fC->Child(List_of_arguments);
            result = compileBits(component, fC, Expression, compileDesign,
                                 reduce, pexpr, instance, false, muteErrors);
          } else if (name == "size") {
            NodeId Expression = fC->Child(List_of_arguments);
            result = compileBits(component, fC, Expression, compileDesign,
                                 reduce, pexpr, instance, true, muteErrors);
          } else if (name == "clog2") {
            result =
                compileClog2(component, fC, List_of_arguments, compileDesign,
                             reduce, pexpr, instance, muteErrors);
          } else if (name == "high" || name == "low" || name == "left" ||
                     name == "right") {
            result =
                compileBound(component, fC, List_of_arguments, compileDesign,
                             reduce, pexpr, instance, muteErrors, name);
          } else if (name == "typename") {
            result = compileTypename(component, fC, List_of_arguments,
                                     compileDesign, reduce, pexpr, instance);
          } else if (fC->Type(Dollar_keyword) == VObjectType::slStringConst ||
                     fC->Type(Dollar_keyword) == VObjectType::paClass_scope) {
            if (fC->Type(Dollar_keyword) == VObjectType::paClass_scope) {
              NodeId Class_type = fC->Child(Dollar_keyword);
              NodeId Class_type_name = fC->Child(Class_type);
              NodeId Class_scope_name = fC->Sibling(Dollar_keyword);
              name.assign(fC->SymName(Class_type_name))
                  .append("::")
                  .append(fC->SymName(Class_scope_name));
            }
            NodeId Select = fC->Sibling(Dollar_keyword);
            if (fC->Type(Select) == VObjectType::paConstant_bit_select ||
                fC->Type(Select) == VObjectType::paBit_select) {
              result = compileExpression(component, fC, Dollar_keyword,
                                         compileDesign, reduce, pexpr, instance,
                                         muteErrors);
            } else {
              bool invalidValue = false;
              UHDM::func_call *fcall = s.MakeFunc_call();
              fcall->VpiName(name);
              fcall->VpiParent(pexpr);
              fC->populateCoreMembers(Dollar_keyword, Dollar_keyword, fcall);

              auto [func, actual_comp] =
                  getTaskFunc(name, component, compileDesign, instance, pexpr);
              fcall->Function(any_cast<function *>(func));
              VectorOfany *args = compileTfCallArguments(
                  component, fC, List_of_arguments, compileDesign, reduce,
                  fcall, instance, muteErrors);
              if (reduce == Reduce::Yes) {
                PathId fileId = fC->getFileId();
                uint32_t lineNumber = fC->Line(nameId);
                if (func == nullptr) {
                  ErrorContainer *errors =
                      compileDesign->getCompiler()->getErrorContainer();
                  SymbolTable *symbols =
                      compileDesign->getCompiler()->getSymbolTable();
                  Location loc(fileId, lineNumber, fC->Column(nameId),
                               symbols->registerSymbol(name));
                  Error err(ErrorDefinition::COMP_UNDEFINED_USER_FUNCTION, loc);
                  errors->addError(err);
                }
                result = EvalFunc(
                    any_cast<function *>(func), args, invalidValue,
                    (instance) ? actual_comp : component, compileDesign,
                    instance, fileId, lineNumber, pexpr);
              }
              if (result == nullptr || invalidValue == true) {
                fcall->Tf_call_args(args);
                result = fcall;
              }
            }
          } else {
            UHDM::sys_func_call *sys = s.MakeSys_func_call();
            sys->VpiName("$" + name);
            sys->VpiParent(pexpr);
            if (VectorOfany *arguments = compileTfCallArguments(
                    component, fC, List_of_arguments, compileDesign, reduce,
                    sys, instance, muteErrors)) {
              sys->Tf_call_args(arguments);
            }
            result = sys;
          }
          break;
        }
        case VObjectType::paData_type:
          // When trying to evaluate type parameters
          if (m_checkForLoops) {
            m_stackLevel--;
          }
          return nullptr;
        case VObjectType::paCycle_delay_const_range_expression: {
          UHDM::range *r = s.MakeRange();
          NodeId lhs = fC->Child(child);
          NodeId rhs = fC->Sibling(lhs);
          r->Left_expr((expr *)compileExpression(component, fC, lhs,
                                                 compileDesign, reduce, r,
                                                 instance, muteErrors));
          r->Right_expr((expr *)compileExpression(component, fC, rhs,
                                                  compileDesign, reduce, r,
                                                  instance, muteErrors));
          fC->populateCoreMembers(parent, parent, r);
          result = r;
          break;
        }
        case VObjectType::paCycle_delay_range: {
          VObjectType type = fC->Type(child);
          operation *operation = s.MakeOperation();
          operation->VpiParent(pexpr);
          UHDM::VectorOfany *operands = s.MakeAnyVec();
          operation->Operands(operands);
          fC->populateCoreMembers(parent, parent, operation);
          int32_t operationType = UhdmWriter::getVpiOpType(type);
          if (NodeId subOp1 = fC->Child(child)) {
            VObjectType subOp1type = fC->Type(subOp1);
            if (subOp1type == VObjectType::paPound_Pound_delay) {
              operationType = vpiUnaryCycleDelayOp;
              if (NodeId subOp2 = fC->Sibling(subOp1)) {
                VObjectType subOp2type = fC->Type(subOp2);
                if (subOp2type == VObjectType::paAssociative_dimension) {
                  operationType = vpiConsecutiveRepeatOp;
                } else if (subOp2type ==
                           VObjectType::paCycle_delay_const_range_expression) {
                  UHDM::range *r = s.MakeRange();
                  NodeId lhs = fC->Child(subOp2);
                  NodeId rhs = fC->Sibling(lhs);
                  r->Left_expr((expr *)compileExpression(
                      component, fC, lhs, compileDesign, reduce, r, instance,
                      muteErrors));
                  r->Right_expr((expr *)compileExpression(
                      component, fC, rhs, compileDesign, reduce, r, instance,
                      muteErrors));
                  fC->populateCoreMembers(subOp2, subOp2, r);
                  operands->push_back(r);
                }
              } else {
                std::string_view val = fC->SymName(subOp1);
                val.remove_prefix(2);
                UHDM::constant *c = s.MakeConstant();
                c->VpiValue(StrCat("UINT:", val));
                c->VpiDecompile(val);
                c->VpiSize(64);
                c->VpiConstType(vpiUIntConst);
                fC->populateCoreMembers(subOp1, subOp1, c);
                operands->push_back(c);
              }
            }
          }
          operation->VpiOpType(operationType);
          if (any *rhs = compileExpression(component, fC, fC->Sibling(child),
                                           compileDesign, reduce, operation,
                                           instance, muteErrors)) {
            operands->push_back(rhs);
          }
          result = operation;
          break;
        }
        case VObjectType::paProperty_expr: {
          expr *subexp =
              (expr *)compileExpression(component, fC, child, compileDesign,
                                        reduce, pexpr, instance, muteErrors);
          if (NodeId sib = fC->Sibling(child)) {
            VObjectType type = fC->Type(sib);
            switch (type) {
              case VObjectType::paOR:
              case VObjectType::paAND:
              case VObjectType::paUNTIL:
              case VObjectType::paS_UNTIL:
              case VObjectType::paUNTIL_WITH:
              case VObjectType::paS_UNTIL_WITH: {
                int32_t optype = UhdmWriter::getVpiOpType(type);
                operation *oper = s.MakeOperation();
                oper->VpiOpType(optype);
                fC->populateCoreMembers(parent, parent, oper);
                UHDM::VectorOfany *operands = s.MakeAnyVec();
                oper->Operands(operands);
                subexp->VpiParent(oper);
                operands->push_back(subexp);
                NodeId nop = fC->Sibling(sib);
                if (expr *nexp = (expr *)compileExpression(
                        component, fC, nop, compileDesign, reduce, oper,
                        instance, muteErrors)) {
                  operands->push_back(nexp);
                }
                result = oper;
                break;
              }
              default:
                break;
            };
          } else {
            result = subexp;
          }
          break;
        }
        case VObjectType::paClass_scope: {
          NodeId Class_type = fC->Child(child);
          NodeId Class_type_name = fC->Child(Class_type);
          NodeId Class_scope_name = fC->Sibling(child);
          std::string name = StrCat(fC->SymName(Class_type_name),
                                    "::", fC->SymName(Class_scope_name));
          ref_obj *ref = s.MakeRef_obj();
          ref->VpiName(name);
          ref->VpiParent(pexpr);
          fC->populateCoreMembers(child, child, ref);
          result = ref;
          break;
        }
        case VObjectType::paACCEPT_ON:
        case VObjectType::paREJECT_ON:
        case VObjectType::paSYNC_ACCEPT_ON:
        case VObjectType::paSYNC_REJECT_ON:
        case VObjectType::paALWAYS:
        case VObjectType::paS_ALWAYS:
        case VObjectType::paEVENTUALLY:
        case VObjectType::paS_EVENTUALLY:
        case VObjectType::paNEXTTIME:
        case VObjectType::paS_NEXTTIME: {
          VObjectType type = childType;
          operation *operation = s.MakeOperation();
          operation->VpiParent(pexpr);
          UHDM::VectorOfany *operands = s.MakeAnyVec();
          operation->Operands(operands);
          fC->populateCoreMembers(parent, parent, operation);
          int32_t operationType = UhdmWriter::getVpiOpType(type);
          operation->VpiOpType(operationType);
          if (any *rhs = compileExpression(component, fC, fC->Sibling(child),
                                           compileDesign, reduce, operation,
                                           instance, muteErrors)) {
            operands->push_back(rhs);
          }
          result = operation;
          break;
        }
        case VObjectType::paClocking_event: {
          if (fC->Type(fC->Sibling(child)) == VObjectType::paSequence_expr) {
            UHDM::clocked_seq *seq = s.MakeClocked_seq();
            if (any *cev = compileExpression(component, fC, fC->Child(child),
                                             compileDesign, reduce, seq,
                                             instance, muteErrors)) {
              seq->VpiClockingEvent((expr *)cev);
            }
            if (any *ex = compileExpression(component, fC, fC->Sibling(child),
                                            compileDesign, reduce, seq,
                                            instance, muteErrors)) {
              seq->VpiSequenceExpr(ex);
            }
            result = seq;
          } else {
            UHDM::clocked_property *prop = s.MakeClocked_property();
            if (any *cev = compileExpression(component, fC, fC->Child(child),
                                             compileDesign, reduce, prop,
                                             instance, muteErrors)) {
              prop->VpiClockingEvent((expr *)cev);
            }
            if (any *ex = compileExpression(component, fC, fC->Sibling(child),
                                            compileDesign, reduce, prop,
                                            instance, muteErrors)) {
              prop->VpiPropertyExpr(ex);
            }
            result = prop;
          }
          break;
        }
        default:
          break;
      }
    } else {
      VObjectType type = fC->Type(parent);
      switch (type) {
        case VObjectType::paIncDec_PlusPlus:
        case VObjectType::paIncDec_MinusMinus:
        case VObjectType::paUnary_Minus:
        case VObjectType::paUnary_Plus:
        case VObjectType::paUnary_Tilda:
        case VObjectType::paUnary_Not:
        case VObjectType::paUnary_BitwOr:
        case VObjectType::paUnary_BitwAnd:
        case VObjectType::paUnary_BitwXor:
        case VObjectType::paUnary_ReductNand:
        case VObjectType::paUnary_ReductNor:
        case VObjectType::paUnary_ReductXnor1:
        case VObjectType::paUnary_ReductXnor2: {
          uint32_t vopType = UhdmWriter::getVpiOpType(type);
          // This is the PREFIX (pre-increment/pre-decrement) case:
          // operator comes before operand. Map to vpiPreIncOp/vpiPreDecOp.
          if (vopType == vpiPostIncOp) vopType = vpiPreIncOp;
          else if (vopType == vpiPostDecOp) vopType = vpiPreDecOp;
          if (vopType) {
            UHDM::operation *op = s.MakeOperation();
            if (attributes != nullptr) {
              op->Attributes(attributes);
              for (auto a : *attributes) a->VpiParent(op);
            }
            op->VpiOpType(vopType);
            op->VpiParent(pexpr);
            fC->populateCoreMembers(parent, parent, op);
            UHDM::VectorOfany *operands = s.MakeAnyVec();
            if (UHDM::any *operand = compileExpression(
                    component, fC, fC->Sibling(parent), compileDesign, reduce,
                    op, instance, muteErrors)) {
              operands->push_back(operand);
            }
            op->Operands(operands);
            result = op;
          }
          break;
        }
        case VObjectType::paNull_keyword: {
          UHDM::constant *c = s.MakeConstant();
          c->VpiValue("UINT:0");
          c->VpiDecompile("0");
          c->VpiSize(64);
          c->VpiConstType(vpiNullConst);
          result = c;
          break;
        }
        case VObjectType::paDollar_keyword: {
          UHDM::constant *c = s.MakeConstant();
          c->VpiConstType(vpiUnboundedConst);
          c->VpiValue("STRING:$");
          c->VpiDecompile("$");
          c->VpiSize(1);
          result = c;
          break;
        }
        case VObjectType::paThis_keyword: {
          // TODO: To be changed to class var
          UHDM::constant *c = s.MakeConstant();
          c->VpiConstType(vpiStringConst);
          c->VpiValue("STRING:this");
          c->VpiDecompile("this");
          c->VpiSize(4);
          result = c;
          break;
        }
        case VObjectType::paSuper_keyword: {
          // TODO: To be changed to class var
          UHDM::constant *c = s.MakeConstant();
          c->VpiConstType(vpiStringConst);
          c->VpiValue("STRING:super");
          c->VpiDecompile("super");
          c->VpiSize(5);
          result = c;
          break;
        }
        case VObjectType::paThis_dot_super: {
          // TODO: To be changed to class var
          UHDM::constant *c = s.MakeConstant();
          c->VpiConstType(vpiStringConst);
          c->VpiValue("STRING:this.super");
          c->VpiDecompile("this.super");
          c->VpiSize(10);
          result = c;
          break;
        }
        case VObjectType::paConstraint_block: {
          // Empty constraint block
          UHDM::constraint *cons = s.MakeConstraint();
          result = cons;
          break;
        }
        case VObjectType::slIntConst:
        case VObjectType::slRealConst:
        case VObjectType::paNumber_1Tickb1:
        case VObjectType::paNumber_1TickB1:
        case VObjectType::paInitVal_1Tickb1:
        case VObjectType::paInitVal_1TickB1:
        case VObjectType::paScalar_1Tickb1:
        case VObjectType::paScalar_1TickB1:
        case VObjectType::pa1:
        case VObjectType::paScalar_Tickb1:
        case VObjectType::paScalar_TickB1:
        case VObjectType::paNumber_Tickb1:
        case VObjectType::paNumber_TickB1:
        case VObjectType::paNumber_Tick1:
        case VObjectType::paNumber_1Tickb0:
        case VObjectType::paNumber_1TickB0:
        case VObjectType::paInitVal_1Tickb0:
        case VObjectType::paInitVal_1TickB0:
        case VObjectType::paScalar_1Tickb0:
        case VObjectType::paScalar_1TickB0:
        case VObjectType::pa0:
        case VObjectType::paScalar_Tickb0:
        case VObjectType::paScalar_TickB0:
        case VObjectType::paNumber_Tickb0:
        case VObjectType::paNumber_TickB0:
        case VObjectType::paNumber_Tick0:
        case VObjectType::paNumber_1TickBX:
        case VObjectType::paNumber_1TickbX:
        case VObjectType::paNumber_1Tickbx:
        case VObjectType::paNumber_1TickBx:
        case VObjectType::paInitVal_1Tickbx:
        case VObjectType::paInitVal_1TickbX:
        case VObjectType::paInitVal_1TickBx:
        case VObjectType::paInitVal_1TickBX:
        case VObjectType::paX:
        case VObjectType::paZ:
        case VObjectType::paTime_literal:
        case VObjectType::slStringLiteral: {
          result = compileConst(fC, parent, s);
          break;
        }
        case VObjectType::slStringConst:
        case VObjectType::paDollar_root_keyword: {
          result = compileComplexFuncCall(component, fC, parent, compileDesign,
                                          reduce, pexpr, instance, muteErrors);
          break;
        }
        case VObjectType::paArray_member_label: {
          ref_obj *ref = s.MakeRef_obj();
          ref->VpiName("default");
          ref->VpiParent(pexpr);
          ref->VpiStructMember(true);
          result = ref;
          break;
        }
        default:
          break;
      }
    }
  }

  NodeId the_node;
  if (child) {
    the_node = child;
  } else {
    the_node = parent;
  }
  if ((result == nullptr) && (muteErrors == false)) {
    VObjectType exprtype = fC->Type(the_node);
    if (exprtype != VObjectType::paEND) {
      ErrorContainer *errors =
          compileDesign->getCompiler()->getErrorContainer();
      SymbolTable *symbols = compileDesign->getCompiler()->getSymbolTable();
      unsupported_expr *exp = s.MakeUnsupported_expr();
      std::string lineText;
      fileSystem->readLine(fC->getFileId(), fC->Line(the_node), lineText);
      Location loc(fC->getFileId(the_node), fC->Line(the_node),
                   fC->Column(the_node),
                   symbols->registerSymbol(
                       StrCat("<", fC->printObject(the_node), "> ", lineText)));
      Error err(ErrorDefinition::UHDM_UNSUPPORTED_EXPR, loc);
      errors->addError(err);
      exp->VpiValue(StrCat("STRING:", lineText));
      fC->populateCoreMembers(the_node, the_node, exp);
      exp->VpiParent(pexpr);
      result = exp;
    }
  }

  if ((result != nullptr) && (reduce == Reduce::Yes)) {
    // Reduce
    bool invalidValue = false;
    if (any *tmp = reduceExpr(result, invalidValue, component, compileDesign,
                              instance, fC->getFileId(the_node),
                              fC->Line(the_node), pexpr, muteErrors)) {
      if (!invalidValue) result = tmp;
    }
  }

  if (result && (result->VpiLineNo() == 0)) {
    if (child) {
      fC->populateCoreMembers(child, child, result);
    } else {
      fC->populateCoreMembers(parent, parent, result);
    }
  }
  if (m_checkForLoops) {
    m_stackLevel--;
  }
  return result;
}

UHDM::any *CompileHelper::compileAssignmentPattern(
    DesignComponent *component, const FileContent *fC,
    NodeId Assignment_pattern, CompileDesign *compileDesign, Reduce reduce,
    UHDM::any *pexpr, ValuedComponentI *instance) {
  FileSystem *const fileSystem = FileSystem::getInstance();
  UHDM::Serializer &s = compileDesign->getSerializer();
  UHDM::any *result = nullptr;
  UHDM::operation *operation = s.MakeOperation();
  UHDM::VectorOfany *operands = s.MakeAnyVec();
  result = operation;
  operation->VpiParent(pexpr);
  operation->VpiOpType(vpiAssignmentPatternOp);
  operation->Operands(operands);
  fC->populateCoreMembers(Assignment_pattern, Assignment_pattern, operation);

  if (component && valuedcomponenti_cast<Package *>(component)) {
    reduce = Reduce::Yes;
  } else if (instance) {
    reduce = Reduce::Yes;
  }
  // Page 1035: For an operation of type vpiAssignmentPatternOp, the operand
  // iteration shall return the expressions as if the assignment pattern were
  // written with the positional notation. Nesting of assignment patterns shall
  // be preserved.

  // We forward the structure without reordering the bits or interpreting,
  // we deviate from the Standard by forwarding the complete spec to the client
  // and letting them do the reordering if need be.
  NodeId Structure_pattern_key = fC->Child(Assignment_pattern);
  bool with_key = true;
  if (fC->Type(Structure_pattern_key) == VObjectType::paExpression ||
      fC->Type(Structure_pattern_key) == VObjectType::paConstant_expression) {
    with_key = false;
  }
  if (!with_key &&
      fC->Type(Structure_pattern_key) == VObjectType::paConstant_expression) {
    // '{2{1}}
    NodeId Expression = Structure_pattern_key;
    if (any *exp = compileExpression(component, fC, Expression, compileDesign,
                                     reduce, operation, instance, false)) {
      Expression = fC->Sibling(Expression);
      operands->push_back(exp);
      operation->VpiOpType(vpiMultiAssignmentPatternOp);
      UHDM::operation *concat = s.MakeOperation();
      concat->VpiOpType(vpiConcatOp);
      fC->populateCoreMembers(Expression, Expression, concat);
      operands->push_back(concat);
      concat->VpiParent(operation);
      UHDM::VectorOfany *suboperands = s.MakeAnyVec();
      concat->Operands(suboperands);
      while (Expression) {
        if (any *val =
                compileExpression(component, fC, Expression, compileDesign,
                                  reduce, concat, instance, false)) {
          suboperands->push_back(val);
        }
        Expression = fC->Sibling(Expression);
      }
    }
    return result;
  }
  while (Structure_pattern_key) {
    NodeId Expression;
    if (!with_key) {
      Expression = Structure_pattern_key;
      if (Expression) {
        // No key '{1,2,...}
        if (any *exp =
                compileExpression(component, fC, Expression, compileDesign,
                                  reduce, operation, instance, false)) {
          operands->push_back(exp);
        }
      }
    } else {
      Expression =
          fC->Sibling(Structure_pattern_key);  // With key '{a: 1, b: 2,...}

      if (Expression) {
        if (any *exp =
                compileExpression(component, fC, Expression, compileDesign,
                                  reduce, operation, instance, false)) {
          if (reduce == Reduce::Yes) {
            if (exp->UhdmType() == uhdmoperation) {
              UHDM::operation *op = (UHDM::operation *)exp;
              bool reduceMore = true;
              int32_t opType = op->VpiOpType();
              if (opType == vpiConcatOp) {
                if (op->Operands()->size() != 1) {
                  reduceMore = false;
                }
              }
              if (reduceMore) {
                bool invalidValue = false;
                if (any *tmp = reduceExpr(
                        exp, invalidValue, component, compileDesign, instance,
                        fileSystem->toPathId(op->VpiFile(),
                                             fC->getSymbolTable()),
                        op->VpiLineNo(), nullptr, true)) {
                  if (!invalidValue) exp = tmp;
                }
              }
            }
          }
          tagged_pattern *pattern = s.MakeTagged_pattern();
          fC->populateCoreMembers(Expression, Expression, pattern);
          if (exp->UhdmType() == uhdmref_obj) {
            ref_obj *ref = (ref_obj *)exp;
            const std::string_view name = ref->VpiName();
            if (any *tmp = getValue(name, component, compileDesign, Reduce::Yes,
                                    instance, fC->getFileId(),
                                    fC->Line(Expression), pattern, true)) {
              exp = tmp;
              if (exp->VpiLineNo() == 0) {
                fC->populateCoreMembers(Expression, Expression, exp);
              }
            }
          }
          pattern->Pattern(exp);
          NodeId Constant_expression = fC->Child(Structure_pattern_key);
          NodeId Constant_primary = fC->Child(Constant_expression);
          if (!Constant_primary) {
            UHDM::string_typespec *tps = s.MakeString_typespec();
            if (fC->Type(Constant_expression) == VObjectType::slStringConst) {
              tps->VpiName(fC->SymName(Constant_expression));
            } else {
              tps->VpiName("default");
            }
            fC->populateCoreMembers(Constant_expression, Constant_expression,
                                    tps);
            tps->VpiParent(pattern);
            if (pattern->Typespec() == nullptr) {
              ref_typespec *rt = s.MakeRef_typespec();
              rt->VpiParent(pattern);
              pattern->Typespec(rt);
            }
            pattern->Typespec()->Actual_typespec(tps);
          } else {
            NodeId Primary_literal = Constant_primary;
            if (fC->Type(Primary_literal) != VObjectType::paPrimary_literal)
              Primary_literal = fC->Child(Constant_primary);
            if (typespec *tps = compileTypespec(component, fC, Primary_literal,
                                                compileDesign, Reduce::Yes,
                                                nullptr, instance, false)) {
              if (pattern->Typespec() == nullptr) {
                ref_typespec *rt = s.MakeRef_typespec();
                rt->VpiParent(pattern);
                pattern->Typespec(rt);
              }
              pattern->Typespec()->Actual_typespec(tps);
            }
          }
          pattern->VpiParent(operation);
          operands->push_back(pattern);
        }
      }
      Structure_pattern_key = fC->Sibling(Structure_pattern_key);
    }

    if (Structure_pattern_key)
      Structure_pattern_key = fC->Sibling(Structure_pattern_key);
  }
  return result;
}

bool CompileHelper::errorOnNegativeConstant(DesignComponent *component,
                                            Value *value,
                                            CompileDesign *compileDesign,
                                            ValuedComponentI *instance) {
  if (value == nullptr) return false;
  const std::string &val = value->uhdmValue();
  return errorOnNegativeConstant(component, val, compileDesign, instance,
                                 BadPathId, 0, 0);
}

bool CompileHelper::errorOnNegativeConstant(DesignComponent *component,
                                            expr *exp,
                                            CompileDesign *compileDesign,
                                            ValuedComponentI *instance) {
  FileSystem *const fileSystem = FileSystem::getInstance();
  if (exp == nullptr) return false;
  if (exp->UhdmType() != uhdmconstant) return false;
  const std::string_view val = exp->VpiValue();
  return errorOnNegativeConstant(
      component, val, compileDesign, instance,
      fileSystem->toPathId(exp->VpiFile(),
                           compileDesign->getCompiler()->getSymbolTable()),
      exp->VpiLineNo(), exp->VpiColumnNo());
}

bool CompileHelper::errorOnNegativeConstant(DesignComponent *component,
                                            std::string_view val,
                                            CompileDesign *compileDesign,
                                            ValuedComponentI *instance,
                                            PathId fileId, uint32_t lineNo,
                                            uint16_t columnNo) {
  FileSystem *const fileSystem = FileSystem::getInstance();
  if (val[4] == '-') {
    std::string instanceName;
    if (instance) {
      if (ModuleInstance *inst =
              valuedcomponenti_cast<ModuleInstance *>(instance)) {
        instanceName = inst->getFullPathName();
      }
    } else if (component) {
      instanceName = component->getName();
    }
    std::string message;
    StrAppend(&message, '"', instanceName, "\"\n");
    SymbolTable *symbols = compileDesign->getCompiler()->getSymbolTable();
    std::string lineText;
    fileSystem->readLine(fileId, lineNo, lineText);
    StrAppend(&message, "             text: ", lineText, "\n");
    StrAppend(&message, "             value: ", val);
    ErrorContainer *errors = compileDesign->getCompiler()->getErrorContainer();
    Location loc(fileId, lineNo, columnNo, symbols->registerSymbol(message));
    Error err(ErrorDefinition::ELAB_NEGATIVE_VALUE, loc);

    bool replay = false;
    // GDB: p replay=true
    if (replay) {
      if (instance) {
        ModuleInstance *inst =
            valuedcomponenti_cast<ModuleInstance *>(instance);
        while (inst) {
          std::cout << "Instance:" << inst->getFullPathName() << " "
                    << inst->getFileId() << "\n";
          std::cout << "Mod: " << inst->getModuleName() << " "
                    << fileSystem->toPath(
                           component->getFileContents()[0]->getFileId())
                    << "\n";

          for (const auto &ps : inst->getMappedValues()) {
            const std::string &name = ps.first;
            Value *val = ps.second.first;
            std::cout << std::string("    " + name + " = " + val->uhdmValue() +
                                     "\n");
          }
          for (const auto &ps : inst->getComplexValues()) {
            const std::string &name = ps.first;
            std::cout << std::string("    " + name + " =  complex\n");
          }
          if (inst->getNetlist() && inst->getNetlist()->param_assigns()) {
            for (auto ps : *inst->getNetlist()->param_assigns()) {
              std::cout << ps->Lhs()->VpiName() << " = "
                        << "\n";
              decompile(ps->Rhs());
            }
          }
          inst = inst->getParent();
        }
      }
    }
    errors->addError(err);
    return true;
  }
  return false;
}

std::vector<UHDM::range *> *CompileHelper::compileRanges(
    DesignComponent *component, const FileContent *fC, NodeId Packed_dimension,
    CompileDesign *compileDesign, Reduce reduce, UHDM::any *pexpr,
    ValuedComponentI *instance, int32_t &size, bool muteErrors) {
  FileSystem *const fileSystem = FileSystem::getInstance();
  UHDM::Serializer &s = compileDesign->getSerializer();
  VectorOfrange *ranges = nullptr;
  size = 0;
  if (Packed_dimension &&
      ((fC->Type(Packed_dimension) == VObjectType::paPacked_dimension) ||
       (fC->Type(Packed_dimension) == VObjectType::paUnpacked_dimension) ||
       (fC->Type(Packed_dimension) == VObjectType::paVariable_dimension) ||
       (fC->Type(Packed_dimension) == VObjectType::paConstant_range) ||
       (fC->Type(Packed_dimension) == VObjectType::paUnsized_dimension))) {
    ranges = s.MakeRangeVec();
    size = 1;
    while (Packed_dimension) {
      NodeId Constant_range = fC->Child(Packed_dimension);
      if (fC->Type(Packed_dimension) == VObjectType::paConstant_range) {
        Constant_range = Packed_dimension;
      }
      if (fC->Type(Constant_range) == VObjectType::paUnpacked_dimension ||
          fC->Type(Constant_range) == VObjectType::paPacked_dimension) {
        Constant_range = fC->Child(Constant_range);
      }
      if (fC->Type(Constant_range) == VObjectType::paConstant_range) {
        // Specified by range
        NodeId lexpr = fC->Child(Constant_range);
        NodeId rexpr = fC->Sibling(lexpr);
        UHDM::range *range = s.MakeRange();

        expr *lexp = any_cast<expr *>(
            compileExpression(component, fC, lexpr, compileDesign, reduce,
                              pexpr, instance, muteErrors));
        if (reduce == Reduce::Yes) {
          if (errorOnNegativeConstant(component, lexp, compileDesign,
                                      instance)) {
            bool replay = false;
            // GDB: p replay=true
            if (replay) {
              compileExpression(component, fC, lexpr, compileDesign, reduce,
                                pexpr, instance, muteErrors);
            }
          }
        }

        if (lexp) {
          lexp->VpiParent(range);
          range->Left_expr(lexp);
        }
        expr *rexp = any_cast<expr *>(
            compileExpression(component, fC, rexpr, compileDesign, reduce,
                              pexpr, instance, muteErrors));
        if (reduce == Reduce::Yes) {
          if (errorOnNegativeConstant(component, rexp, compileDesign,
                                      instance)) {
            bool replay = false;
            // GDB: p replay=true
            if (replay) {
              compileExpression(component, fC, rexpr, compileDesign, reduce,
                                pexpr, instance, muteErrors);
            }
          }
        }
        if (rexp) {
          rexp->VpiParent(range);
          range->Right_expr(rexp);
        }
        if ((lexp) && (rexp)) {
          if (reduce == Reduce::Yes) {
            UHDM::ExprEval eval;
            bool invalidValue = false;
            lexp = reduceExpr(lexp, invalidValue, component, compileDesign,
                              instance, fC->getFileId(), fC->Line(lexpr), pexpr,
                              muteErrors);
            rexp = reduceExpr(rexp, invalidValue, component, compileDesign,
                              instance, fC->getFileId(), fC->Line(rexpr), pexpr,
                              muteErrors);
            uint64_t lint = eval.get_value(invalidValue, lexp);
            uint64_t rint = eval.get_value(invalidValue, rexp);
            if (lexp) {
              lexp->VpiParent(range);
              range->Left_expr(lexp);
            }
            if (rexp) {
              rexp->VpiParent(range);
              range->Right_expr(rexp);
            }
            if (!invalidValue) {
              uint64_t tmp = (lint > rint) ? lint - rint + 1 : rint - lint + 1;
              size = size * tmp;
            }
          }
        }
        fC->populateCoreMembers(Packed_dimension, Packed_dimension, range);
        ranges->push_back(range);
        range->VpiParent(pexpr);
      } else if (fC->Type(Constant_range) ==
                 VObjectType::paConstant_expression) {
        // Specified by size
        NodeId rexpr = Constant_range;
        UHDM::range *range = s.MakeRange();
        range->VpiParent(pexpr);
        fC->populateCoreMembers(Constant_range, Constant_range, range);

        constant *lexpc = s.MakeConstant();
        lexpc->VpiConstType(vpiUIntConst);
        lexpc->VpiSize(64);
        lexpc->VpiValue("UINT:0");
        lexpc->VpiDecompile("0");
        range->Left_expr(lexpc);
        lexpc->VpiParent(range);
        if (reduce == Reduce::Yes) {
          Value *rightV = m_exprBuilder.evalExpr(fC, rexpr, instance, true);
          if (rightV->isValid()) {
            int64_t rint = rightV->getValueL();
            size = size * rint;
          }
        }

        expr *rexp = any_cast<expr *>(
            compileExpression(component, fC, rexpr, compileDesign, reduce,
                              range, instance, muteErrors));
        bool associativeArray = false;
        if (rexp && rexp->UhdmType() == uhdmconstant) {
          constant *c = (constant *)rexp;
          const std::string_view val = c->VpiValue();
          if ((reduce == Reduce::Yes) &&
              ((val == "UINT:0") || (val == "INT:0") || (val[4] == '-'))) {
            ErrorContainer *errors =
                compileDesign->getCompiler()->getErrorContainer();
            SymbolTable *symbols =
                compileDesign->getCompiler()->getSymbolTable();
            std::string instanceName;
            if (instance) {
              if (ModuleInstance *inst =
                      valuedcomponenti_cast<ModuleInstance *>(instance)) {
                instanceName = inst->getFullPathName();
              }
            } else if (component) {
              instanceName = component->getName();
            }
            std::string message;
            StrAppend(&message, '"', instanceName, "\"\n");
            std::string lineText;
            fileSystem->readLine(fC->getFileId(), fC->Line(rexpr), lineText);
            StrAppend(&message, "             text: ", lineText, "\n");
            StrAppend(&message, "             value: ", val);

            Location loc(fC->getFileId(), fC->Line(rexpr), fC->Column(rexpr),
                         symbols->registerSymbol(message));
            Error err(ErrorDefinition::ELAB_ILLEGAL_ZERO_VALUE, loc);
            errors->addError(err);
          }
          if (c->VpiConstType() == vpiUnboundedConst) associativeArray = true;
        }
        if (rexp && (rexp->UhdmType() == uhdmref_obj) &&
            (reduce == Reduce::Yes)) {
          if (typespec *assoc_tps =
                  compileTypespec(component, fC, rexpr, compileDesign, reduce,
                                  nullptr, instance, true)) {
            associativeArray = true;
            UHDM::range *range = s.MakeRange();

            constant *lexpc = s.MakeConstant();
            lexpc->VpiConstType(vpiUIntConst);
            lexpc->VpiSize(64);
            lexpc->VpiValue("UINT:0");
            lexpc->VpiDecompile("0");
            lexpc->VpiParent(range);
            fC->populateCoreMembers(Packed_dimension, Packed_dimension, lexpc);
            lexpc->VpiEndColumnNo(fC->Column(Packed_dimension) + 1);
            range->Left_expr(lexpc);

            constant *rexpc = s.MakeConstant();
            rexpc->VpiConstType(vpiStringConst);
            rexpc->VpiSize(0);
            rexpc->VpiValue("STRING:associative");
            rexpc->VpiDecompile("associative");
            rexpc->VpiParent(range);
            fC->populateCoreMembers(Packed_dimension, Packed_dimension, range);
            fC->populateCoreMembers(Packed_dimension, Packed_dimension, rexpc);
            rexpc->VpiEndColumnNo(fC->Column(Packed_dimension) + 1);
            range->Right_expr(rexpc);

            ref_typespec *assoc_tps_rt = s.MakeRef_typespec();
            assoc_tps_rt->VpiParent(rexpc);
            assoc_tps_rt->Actual_typespec(assoc_tps);
            rexpc->Typespec(assoc_tps_rt);

            range->VpiParent(pexpr);
            ranges->push_back(range);
            Packed_dimension = fC->Sibling(Packed_dimension);
            continue;
          }
        }
        if (!associativeArray) {
          operation *op = s.MakeOperation();  // Decr by 1
          op->VpiOpType(vpiSubOp);
          op->Operands(s.MakeAnyVec());
          op->Operands()->push_back(rexp);
          fC->populateCoreMembers(Constant_range, Constant_range, op);

          constant *one = s.MakeConstant();
          one->VpiValue("INT:1");
          one->VpiConstType(vpiIntConst);
          one->VpiSize(64);
          op->Operands()->push_back(one);
          rexp->VpiParent(op);
          rexp = op;
        }

        if (rexp) {
          rexp->VpiParent(range);
          range->Right_expr(rexp);
        }
        fC->populateCoreMembers(Constant_range, Constant_range, range);
        ranges->push_back(range);
        range->VpiParent(pexpr);
      } else if ((fC->Type(fC->Child(Packed_dimension)) ==
                  VObjectType::paUnsized_dimension) ||
                 (fC->Type(Packed_dimension) ==
                  VObjectType::paUnsized_dimension)) {
        UHDM::range *range = s.MakeRange();

        fC->populateCoreMembers(Packed_dimension, Packed_dimension, range);
        constant *lexpc = s.MakeConstant();
        lexpc->VpiConstType(vpiUIntConst);
        lexpc->VpiSize(64);
        lexpc->VpiValue("UINT:0");
        lexpc->VpiDecompile("0");
        fC->populateCoreMembers(Packed_dimension, Packed_dimension, lexpc);
        lexpc->VpiEndColumnNo(fC->Column(Packed_dimension) + 1);
        range->Left_expr(lexpc);
        lexpc->VpiParent(range);

        constant *rexpc = s.MakeConstant();
        rexpc->VpiConstType(vpiStringConst);
        rexpc->VpiSize(0);
        rexpc->VpiValue("STRING:unsized");
        rexpc->VpiDecompile("unsized");
        fC->populateCoreMembers(Packed_dimension, Packed_dimension, rexpc);
        rexpc->VpiEndColumnNo(fC->Column(Packed_dimension) + 1);
        range->Right_expr(rexpc);
        range->VpiParent(pexpr);
        rexpc->VpiParent(range);
        ranges->push_back(range);
      } else if (fC->Type(fC->Child(Packed_dimension)) ==
                 VObjectType::paAssociative_dimension) {
        NodeId DataType = fC->Child(fC->Child(Packed_dimension));
        UHDM::range *range = s.MakeRange();
        fC->populateCoreMembers(Packed_dimension, Packed_dimension, range);

        constant *lexpc = s.MakeConstant();
        lexpc->VpiConstType(vpiUIntConst);
        lexpc->VpiSize(64);
        lexpc->VpiValue("UINT:0");
        lexpc->VpiDecompile("0");
        lexpc->VpiParent(range);
        range->Left_expr(lexpc);

        constant *rexpc = s.MakeConstant();
        rexpc->VpiConstType(vpiStringConst);
        rexpc->VpiSize(0);
        rexpc->VpiValue("STRING:associative");
        rexpc->VpiDecompile("associative");
        rexpc->VpiParent(range);
        range->Right_expr(rexpc);

        if (typespec *assoc_tps =
                compileTypespec(component, fC, DataType, compileDesign, reduce,
                                nullptr, instance, true)) {
          ref_typespec *assoc_tps_rt = s.MakeRef_typespec();
          assoc_tps_rt->VpiParent(rexpc);
          assoc_tps_rt->Actual_typespec(assoc_tps);
          rexpc->Typespec(assoc_tps_rt);
        }

        range->VpiParent(pexpr);
        ranges->push_back(range);
      }
      Packed_dimension = fC->Sibling(Packed_dimension);
    }
  }
  return ranges;
}

UHDM::any *CompileHelper::compilePartSelectRange(
    DesignComponent *component, const FileContent *fC, NodeId Constant_range,
    std::string_view name, CompileDesign *compileDesign, Reduce reduce,
    UHDM::any *pexpr, ValuedComponentI *instance, bool muteErrors) {
  UHDM::Serializer &s = compileDesign->getSerializer();
  UHDM::any *result = nullptr;
  NodeId Constant_expression = fC->Child(Constant_range);
  if (fC->Type(Constant_range) == VObjectType::paConstant_range) {
    UHDM::part_select *part_select = s.MakePart_select();
    if (name.find("::") != std::string::npos) {
      part_select->VpiFullName(name);
    }
    fC->populateCoreMembers(Constant_expression,
                            fC->Sibling(Constant_expression), part_select);
    if (UHDM::expr *lexp = (expr *)compileExpression(
            component, fC, Constant_expression, compileDesign, Reduce::No,
            part_select, instance)) {
      part_select->Left_range(lexp);
    }
    if (UHDM::expr *rexp = (expr *)compileExpression(
            component, fC, fC->Sibling(Constant_expression), compileDesign,
            Reduce::No, part_select, instance)) {
      part_select->Right_range(rexp);
    }
    if (!name.empty() && (name != "CREATE_UNNAMED_PARENT")) {
      part_select->VpiName(name);
      part_select->VpiDefName(name);
    }
    part_select->VpiParent(pexpr);
    part_select->VpiConstantSelect(true);
    result = part_select;
  } else {
    // constant_indexed_range
    UHDM::indexed_part_select *part_select = s.MakeIndexed_part_select();
    if (UHDM::expr *lexp = (expr *)compileExpression(
            component, fC, Constant_expression, compileDesign, reduce,
            part_select, instance, muteErrors)) {
      part_select->Base_expr(lexp);
    }
    NodeId op = fC->Sibling(Constant_expression);
    if (UHDM::expr *rexp = (expr *)compileExpression(
            component, fC, fC->Sibling(op), compileDesign, reduce, part_select,
            instance, muteErrors)) {
      part_select->Width_expr(rexp);
    }
    if (fC->Type(op) == VObjectType::paIncPartSelectOp)
      part_select->VpiIndexedPartSelectType(vpiPosIndexed);
    else
      part_select->VpiIndexedPartSelectType(vpiNegIndexed);
    if (!name.empty() && (name != "CREATE_UNNAMED_PARENT")) {
      part_select->VpiName(name);
      part_select->VpiDefName(name);
    }
    part_select->VpiParent(pexpr);
    part_select->VpiConstantSelect(true);
    result = part_select;

    if ((reduce == Reduce::Yes) &&
        (part_select->Base_expr()->UhdmType() == uhdmconstant) &&
        (part_select->Width_expr()->UhdmType() == uhdmconstant)) {
      bool invalidValue = false;
      result = reduceExpr(result, invalidValue, component, compileDesign,
                          instance, BadPathId, 0, pexpr, muteErrors);
    }
  }
  if (result != nullptr) {
    fC->populateCoreMembers(Constant_range, Constant_range, result);
  }
  return result;
}

uint64_t CompileHelper::Bits(const UHDM::any *typespec, bool &invalidValue,
                             DesignComponent *component,
                             CompileDesign *compileDesign, Reduce reduce,
                             ValuedComponentI *instance, PathId fileId,
                             uint32_t lineNumber, bool sizeMode) {
  if (loopDetected(fileId, lineNumber, compileDesign, instance)) {
    return 0;
  }
  if (m_checkForLoops) {
    m_stackLevel++;
  }
  if (typespec) {
    const std::string_view name = typespec->VpiName();
    if (name.find("::") != std::string::npos) {
      std::vector<std::string_view> res;
      StringUtils::tokenizeMulti(name, "::", res);
      if (res.size() > 1) {
        const std::string_view packName = res[0];
        Design *design = compileDesign->getCompiler()->getDesign();
        if (Package *pack = design->getPackage(packName)) {
          component = pack;
        }
      }
    }
  }

  UHDM::GetObjectFunctor getObjectFunctor =
      [&](std::string_view name, const any *inst,
          const any *pexpr) -> UHDM::any * {
    return getObject(name, component, compileDesign, instance, pexpr);
  };
  UHDM::GetObjectFunctor getValueFunctor =
      [&](std::string_view name, const any *inst,
          const any *pexpr) -> UHDM::any * {
    return (expr *)getValue(name, component, compileDesign, Reduce::Yes,
                            instance, fileId, lineNumber, (any *)pexpr, false);
  };
  UHDM::GetTaskFuncFunctor getTaskFuncFunctor =
      [&](std::string_view name, const any *inst) -> UHDM::task_func * {
    auto ret = getTaskFunc(name, component, compileDesign, instance, nullptr);
    return ret.first;
  };
  UHDM::ExprEval eval;
  eval.setGetObjectFunctor(getObjectFunctor);
  eval.setGetValueFunctor(getValueFunctor);
  eval.setGetTaskFuncFunctor(getTaskFuncFunctor);
  if (m_exprEvalPlaceHolder == nullptr) {
    m_exprEvalPlaceHolder = compileDesign->getSerializer().MakeModule_inst();
    m_exprEvalPlaceHolder->Param_assigns(
        compileDesign->getSerializer().MakeParam_assignVec());
  } else {
    m_exprEvalPlaceHolder->Param_assigns()->erase(
        m_exprEvalPlaceHolder->Param_assigns()->begin(),
        m_exprEvalPlaceHolder->Param_assigns()->end());
  }
  uint64_t size = eval.size(typespec, invalidValue, m_exprEvalPlaceHolder,
                            nullptr, !sizeMode);
  if (m_checkForLoops) {
    m_stackLevel--;
  }
  return size;
}

const typespec *getMemberTypespec(const typespec *tpss,
                                  const std::vector<std::string> &suffixes,
                                  uint32_t index) {
  const typespec *result = nullptr;
  if (tpss == nullptr) return result;
  if (tpss->UhdmType() == uhdmstruct_typespec) {
    const struct_typespec *ts = (const struct_typespec *)tpss;
    for (typespec_member *memb : *ts->Members()) {
      if (memb->VpiName() == suffixes[index]) {
        if (const UHDM::ref_typespec *rt = memb->Typespec()) {
          result = rt->Actual_typespec();
        }
        if (result && (index < (suffixes.size() - 1))) {
          if (result->UhdmType() == uhdmstruct_typespec) {
            result = getMemberTypespec(result, suffixes, index + 1);
          }
        }
        break;
      }
    }
  }
  return result;
}

const typespec *CompileHelper::getTypespec(DesignComponent *component,
                                           const FileContent *fC, NodeId id,
                                           CompileDesign *compileDesign,
                                           Reduce reduce,
                                           ValuedComponentI *instance) {
  if (loopDetected(fC->getFileId(), fC->Line(id), compileDesign, instance)) {
    return nullptr;
  }
  UHDM::Serializer &s = compileDesign->getSerializer();
  const DataType *dtype = nullptr;
  const typespec *result = nullptr;
  std::string basename;
  std::vector<std::string> suffixnames;
  switch (fC->Type(id)) {
    case VObjectType::paIntegerAtomType_Byte: {
      result = s.MakeByte_typespec();
      break;
    }
    case VObjectType::paIntegerAtomType_Int: {
      result = s.MakeInt_typespec();
      break;
    }
    case VObjectType::paIntegerAtomType_Integer: {
      result = s.MakeInteger_typespec();
      break;
    }
    case VObjectType::paIntegerAtomType_LongInt: {
      result = s.MakeLong_int_typespec();
      break;
    }
    case VObjectType::paIntegerAtomType_Shortint: {
      result = s.MakeShort_int_typespec();
      break;
    }
    case VObjectType::paIntegerAtomType_Time: {
      result = s.MakeTime_typespec();
      break;
    }
    case VObjectType::slStringConst: {
      basename = fC->SymName(id);
      NodeId suffix = fC->Sibling(id);
      while (suffix && (fC->Type(suffix) == VObjectType::slStringConst)) {
        suffixnames.emplace_back(fC->SymName(suffix));
        suffix = fC->Sibling(suffix);
      }
      break;
    }
    case VObjectType::paComplex_func_call: {
      UHDM::any *exp =
          compileExpression(component, fC, fC->Parent(id), compileDesign,
                            reduce, nullptr, instance, false);
      if (exp) {
        if (exp->UhdmType() == uhdmhier_path) {
          bool invalidValue = false;
          result = (typespec *)decodeHierPath(
              (hier_path *)exp, invalidValue, component, compileDesign, reduce,
              instance, fC->getFileId(), fC->Line(id), nullptr, false, true);
        } else if (exp->UhdmType() == uhdmbit_select) {
          bit_select *select = (bit_select *)exp;
          basename = select->VpiName();
        } else if (exp->UhdmType() == uhdmref_obj) {
          basename = exp->VpiName();
          if (basename.find("::") != std::string::npos) {
            std::vector<std::string_view> res;
            StringUtils::tokenizeMulti(basename, "::", res);
            if (res.size() > 1) {
              const std::string_view packName = res[0];
              const std::string_view typeName = res[1];
              Package *p =
                  compileDesign->getCompiler()->getDesign()->getPackage(
                      packName);
              if (p) {
                dtype = p->getDataType(typeName);
              }
            }
          }
        } else if (exp->UhdmType() == uhdmvar_select) {
          var_select *select = (var_select *)exp;
          basename = select->VpiName();
        } else {
          basename = exp->VpiName();
        }
      }
      break;
    }
    case VObjectType::paIntVec_TypeLogic: {
      result = s.MakeLogic_typespec();
      break;
    }
    case VObjectType::paIntVec_TypeBit: {
      result = s.MakeBit_typespec();
      break;
    }
    case VObjectType::paIntVec_TypeReg: {
      result = s.MakeLogic_typespec();
      break;
    }
    case VObjectType::paClass_scope: {
      NodeId Class_type = fC->Child(id);
      NodeId Class_type_name = fC->Child(Class_type);
      NodeId Class_scope_name = fC->Sibling(id);
      basename.assign(fC->SymName(Class_type_name))
          .append("::")
          .append(fC->SymName(Class_scope_name));
      Package *p = compileDesign->getCompiler()->getDesign()->getPackage(
          fC->SymName(Class_type_name));
      if (p) {
        dtype = p->getDataType(fC->SymName(Class_scope_name));
      } else {
      }
      break;
    }
    case VObjectType::paPackage_scope: {
      const std::string_view packageName = fC->SymName(fC->Child(id));
      const std::string_view n = fC->SymName(fC->Sibling(id));
      basename.assign(packageName).append("::").append(n);
      Package *p =
          compileDesign->getCompiler()->getDesign()->getPackage(packageName);
      if (p) {
        dtype = p->getDataType(n);
      }
      break;
    }
    default:
      break;
  }

  if (dtype == nullptr) {
    if (component) dtype = component->getDataType(basename);
  }
  if ((dtype == nullptr) && component) {
    Signal *sig = nullptr;
    for (auto s : component->getPorts()) {
      if (s->getName() == basename) {
        sig = s;
        break;
      }
    }
    if (sig == nullptr) {
      for (auto s : component->getSignals()) {
        if (s->getName() == basename) {
          sig = s;
          break;
        }
      }
    }
    if (sig) {
      if (NodeId sigTypeId = sig->getTypeSpecId()) {
        result = compileTypespec(component, fC, sigTypeId, compileDesign,
                                 reduce, nullptr, instance, true);
        NodeId Unpacked_dimension = sig->getUnpackedDimension();
        if (fC->Type(Unpacked_dimension) != VObjectType::sl_INVALID_) {
          array_typespec *array = s.MakeArray_typespec();
          int32_t size;
          if (VectorOfrange *ranges = compileRanges(
                  component, fC, Unpacked_dimension, compileDesign, reduce,
                  nullptr, instance, size, false)) {
            array->Ranges(ranges);
          }
          ref_typespec *rt = s.MakeRef_typespec();
          rt->VpiParent(array);
          rt->Actual_typespec(const_cast<UHDM::typespec *>(result));
          array->Elem_typespec(rt);
          fC->populateCoreMembers(
              sigTypeId, Unpacked_dimension ? Unpacked_dimension : sigTypeId,
              array);
          result = array;
        }
      } else {
        NodeId Packed_dimension = sig->getPackedDimension();
        if (fC->Type(Packed_dimension) != VObjectType::sl_INVALID_) {
          NodeId DataType = fC->Parent(Packed_dimension);
          result = compileTypespec(component, fC, DataType, compileDesign,
                                   reduce, nullptr, instance, false);
        }
        NodeId Unpacked_dimension = sig->getUnpackedDimension();
        if (fC->Type(Unpacked_dimension) != VObjectType::sl_INVALID_) {
          array_typespec *array = s.MakeArray_typespec();
          int32_t size;
          if (VectorOfrange *ranges = compileRanges(
                  component, fC, Unpacked_dimension, compileDesign, reduce,
                  nullptr, instance, size, false)) {
            array->Ranges(ranges);
          }
          if (result == nullptr) {
            result =
                compileBuiltinTypespec(component, fC, sig->getNodeId(),
                                       sig->getType(), compileDesign, nullptr);
          }
          ref_typespec *rt = s.MakeRef_typespec();
          rt->VpiParent(array);
          rt->Actual_typespec(const_cast<UHDM::typespec *>(result));
          array->Elem_typespec(rt);
          result = array;
        }
      }
    }
  }
  while (dtype) {
    const TypeDef *typed = datatype_cast<const TypeDef *>(dtype);
    if (typed) {
      const DataType *dt = typed->getDataType();
      if (const Enum *en = datatype_cast<const Enum *>(dt)) {
        result = en->getTypespec();
        break;
      }
      if (const Struct *st = datatype_cast<const Struct *>(dt)) {
        result = st->getTypespec();
        if (!suffixnames.empty()) {
          result = getMemberTypespec(result, suffixnames, 0);
        }
        break;
      }
      if (const Union *un = datatype_cast<const Union *>(dt)) {
        result = un->getTypespec();
        break;
      }
      if (const SimpleType *sit = datatype_cast<const SimpleType *>(dt)) {
        result = sit->getTypespec();
        break;
      }
    }
    dtype = dtype->getDefinition();
  }

  if (result == nullptr) {
    if (ModuleInstance *inst =
            valuedcomponenti_cast<ModuleInstance *>(instance)) {
      if (Netlist *netlist = inst->getNetlist()) {
        if (netlist->ports()) {
          for (port *p : *netlist->ports()) {
            if (p->VpiName() == basename) {
              const typespec *tps = nullptr;
              if (const UHDM::ref_typespec *rt = p->Typespec()) {
                tps = rt->Actual_typespec();
              }
              if (!suffixnames.empty()) {
                result = getMemberTypespec(tps, suffixnames, 0);
              }
            }
            if (result) break;
          }
        }
        if (netlist->param_assigns()) {
          for (param_assign *pass : *netlist->param_assigns()) {
            const any *param = pass->Lhs();
            if (param->VpiName() == basename) {
              if (param->UhdmType() == uhdmparameter) {
                parameter *p = (parameter *)param;
                if (const UHDM::ref_typespec *rt = p->Typespec()) {
                  result = rt->Actual_typespec();
                }
              } else {
                type_parameter *p = (type_parameter *)param;
                if (const UHDM::ref_typespec *rt = p->Typespec()) {
                  result = rt->Actual_typespec();
                }
              }
              break;
            }
          }
        }
      }
    }
  } else {
    if (!suffixnames.empty()) {
      result = getMemberTypespec(result, suffixnames, 0);
    }
  }
  return result;
}

UHDM::any *CompileHelper::compileBits(
    DesignComponent *component, const FileContent *fC, NodeId List_of_arguments,
    CompileDesign *compileDesign, Reduce reduce, UHDM::any *pexpr,
    ValuedComponentI *instance, bool sizeMode, bool muteErrors) {
  UHDM::Serializer &s = compileDesign->getSerializer();
  UHDM::any *result = nullptr;
  NodeId Expression = List_of_arguments;
  if (fC->Type(Expression) == VObjectType::paList_of_arguments) {
    Expression = fC->Child(Expression);
  } else if (fC->Type(Expression) == VObjectType::paData_type) {
    Expression = fC->Child(Expression);
  }
  NodeId typeSpecId;
  uint64_t bits = 0;
  bool invalidValue = false;
  const typespec *tps = nullptr;
  const any *exp = nullptr;
  switch (fC->Type(Expression)) {
    case VObjectType::paIntegerAtomType_Byte:
    case VObjectType::paIntegerAtomType_Int:
    case VObjectType::paIntegerAtomType_Integer:
    case VObjectType::paIntegerAtomType_LongInt:
    case VObjectType::paIntegerAtomType_Shortint:
    case VObjectType::paIntegerAtomType_Time:
    case VObjectType::paIntVec_TypeLogic:
    case VObjectType::paIntVec_TypeBit:
    case VObjectType::paIntVec_TypeReg:
      typeSpecId = Expression;
      break;
    default: {
      NodeId Primary = fC->Child(Expression);
      NodeId Primary_literal = fC->Child(Primary);
      if (fC->Type(Primary_literal) == VObjectType::paConcatenation) {
        NodeId ConcatExpression = fC->Child(Primary_literal);
        while (ConcatExpression) {
          NodeId Primary = fC->Child(ConcatExpression);
          NodeId Primary_literal = fC->Child(Primary);
          NodeId StringConst = fC->Child(Primary_literal);
          typeSpecId = StringConst;
          tps = getTypespec(component, fC, typeSpecId, compileDesign, reduce,
                            instance);
          if (m_elabMode && (reduce == Reduce::No) && tps) {
            UHDM::ExprEval eval;
            if (eval.isFullySpecified(tps)) {
              reduce = Reduce::Yes;
            }
          }
          if ((reduce == Reduce::Yes) && tps)
            bits += Bits(tps, invalidValue, component, compileDesign, reduce,
                         instance, fC->getFileId(typeSpecId),
                         fC->Line(typeSpecId), sizeMode);
          ConcatExpression = fC->Sibling(ConcatExpression);
        }
      } else if (fC->Type(Primary_literal) ==
                 VObjectType::paComplex_func_call) {
        typeSpecId = Primary_literal;
      } else {
        NodeId StringConst = fC->Child(Primary_literal);
        typeSpecId = StringConst;
      }
    }
  }

  if (bits == 0) {
    tps =
        getTypespec(component, fC, typeSpecId, compileDesign, reduce, instance);
    if (m_elabMode && (reduce == Reduce::No) && tps) {
      UHDM::ExprEval eval;
      if (eval.isFullySpecified(tps)) {
        reduce = Reduce::Yes;
      }
    }
    if ((reduce == Reduce::Yes) && tps)
      bits = Bits(tps, invalidValue, component, compileDesign, reduce, instance,
                  fC->getFileId(typeSpecId), fC->Line(typeSpecId), sizeMode);

    if ((reduce == Reduce::Yes) && (!tps)) {
      exp = compileExpression(component, fC, Expression, compileDesign,
                              Reduce::Yes, pexpr, instance, true);
      if (exp && typeSpecId) {
        bits =
            Bits(exp, invalidValue, component, compileDesign, reduce, instance,
                 fC->getFileId(typeSpecId), fC->Line(typeSpecId), sizeMode);
      }
    }
  }

  if ((reduce == Reduce::Yes) && tps && (!invalidValue)) {
    UHDM::constant *c = s.MakeConstant();
    c->VpiValue("UINT:" + std::to_string(bits));
    c->VpiDecompile(std::to_string(bits));
    c->VpiConstType(vpiUIntConst);
    c->VpiSize(64);
    result = c;
  } else if ((reduce == Reduce::Yes) && exp && (!invalidValue)) {
    UHDM::constant *c = s.MakeConstant();
    c->VpiValue("UINT:" + std::to_string(bits));
    c->VpiDecompile(std::to_string(bits));
    c->VpiConstType(vpiUIntConst);
    c->VpiSize(64);
    result = c;
  } else if (sizeMode) {
    UHDM::sys_func_call *sys = s.MakeSys_func_call();
    sys->VpiName("$size");
    sys->VpiParent(pexpr);
    if (VectorOfany *arguments = compileTfCallArguments(
            component, fC, List_of_arguments, compileDesign, reduce, sys,
            instance, muteErrors)) {
      sys->Tf_call_args(arguments);
    }
    result = sys;
  } else {
    UHDM::sys_func_call *sys = s.MakeSys_func_call();
    sys->VpiName("$bits");
    sys->VpiParent(pexpr);
    if (VectorOfany *arguments = compileTfCallArguments(
            component, fC, List_of_arguments, compileDesign, reduce, sys,
            instance, muteErrors)) {
      sys->Tf_call_args(arguments);
    }
    result = sys;
  }

  return result;
}

UHDM::any *CompileHelper::compileTypename(DesignComponent *component,
                                          const FileContent *fC,
                                          NodeId Expression,
                                          CompileDesign *compileDesign,
                                          Reduce reduce, UHDM::any *pexpr,
                                          ValuedComponentI *instance) {
  UHDM::Serializer &s = compileDesign->getSerializer();
  UHDM::any *result = nullptr;
  UHDM::constant *c = s.MakeConstant();
  if (fC->Type(Expression) == VObjectType::paData_type) {
    Expression = fC->Child(Expression);
    if (fC->Type(Expression) == VObjectType::paVIRTUAL)
      Expression = fC->Sibling(Expression);
  }
  VObjectType type = fC->Type(Expression);
  switch (type) {
    case VObjectType::paIntVec_TypeLogic:
      c->VpiValue("STRING:logic");
      c->VpiDecompile("logic");
      c->VpiConstType(vpiStringConst);
      result = c;
      break;
    case VObjectType::paIntVec_TypeBit:
      c->VpiValue("STRING:bit");
      c->VpiDecompile("bit");
      c->VpiConstType(vpiStringConst);
      result = c;
      break;
    case VObjectType::paIntVec_TypeReg:
      c->VpiValue("STRING:reg");
      c->VpiDecompile("reg");
      c->VpiConstType(vpiStringConst);
      result = c;
      break;
    case VObjectType::paIntegerAtomType_Byte:
      c->VpiValue("STRING:byte");
      c->VpiDecompile("byte");
      c->VpiConstType(vpiStringConst);
      result = c;
      break;
    case VObjectType::paIntegerAtomType_Shortint:
      c->VpiValue("STRING:shortint");
      c->VpiDecompile("shortint");
      c->VpiConstType(vpiStringConst);
      result = c;
      break;
    case VObjectType::paIntegerAtomType_Int:
      c->VpiValue("STRING:int");
      c->VpiDecompile("int");
      c->VpiConstType(vpiStringConst);
      result = c;
      break;
    case VObjectType::paIntegerAtomType_Integer:
      c->VpiValue("STRING:integer");
      c->VpiDecompile("integer");
      c->VpiConstType(vpiStringConst);
      result = c;
      break;
    case VObjectType::paIntegerAtomType_LongInt:
      c->VpiValue("STRING:longint");
      c->VpiDecompile("longint");
      c->VpiConstType(vpiStringConst);
      result = c;
      break;
    case VObjectType::paIntegerAtomType_Time:
      c->VpiValue("STRING:time");
      c->VpiDecompile("time");
      c->VpiConstType(vpiStringConst);
      result = c;
      break;
    case VObjectType::paNonIntType_ShortReal:
      c->VpiValue("STRING:shortreal");
      c->VpiDecompile("shortreal");
      c->VpiConstType(vpiStringConst);
      result = c;
      break;
    case VObjectType::paNonIntType_Real:
      c->VpiValue("STRING:real");
      c->VpiDecompile("real");
      c->VpiConstType(vpiStringConst);
      result = c;
      break;
    case VObjectType::paNonIntType_RealTime:
      c->VpiValue("STRING:realtime");
      c->VpiDecompile("realtime");
      c->VpiConstType(vpiStringConst);
      result = c;
      break;
    default:
      UHDM::sys_func_call *sys = s.MakeSys_func_call();
      sys->VpiName("$typename");
      sys->VpiParent(pexpr);
      result = sys;
      const std::string_view arg = fC->SymName(Expression);
      c->VpiValue(StrCat("STRING:", arg));
      c->VpiDecompile(arg);
      c->VpiConstType(vpiStringConst);
      c->VpiParent(sys);
      break;
  }
  return result;
}

UHDM::any *CompileHelper::compileBound(
    DesignComponent *component, const FileContent *fC, NodeId List_of_arguments,
    CompileDesign *compileDesign, Reduce reduce, UHDM::any *pexpr,
    ValuedComponentI *instance, bool muteErrors, std::string_view name) {
  UHDM::Serializer &s = compileDesign->getSerializer();
  UHDM::any *result = nullptr;
  NodeId Expression = List_of_arguments;
  if (fC->Type(Expression) == VObjectType::paList_of_arguments) {
    Expression = fC->Child(Expression);
  }
  if (expr *operand =
          (expr *)compileExpression(component, fC, Expression, compileDesign,
                                    Reduce::No, pexpr, instance, muteErrors)) {
    const typespec *ts = nullptr;
    if (const UHDM::ref_typespec *rt = operand->Typespec()) {
      ts = rt->Actual_typespec();
    }
    VectorOfrange *ranges = nullptr;
    if (ts) {
      switch (ts->UhdmType()) {
        case uhdmbit_typespec: {
          bit_typespec *bts = (bit_typespec *)ts;
          ranges = bts->Ranges();
          break;
        }
        case uhdmint_typespec: {
          int_typespec *bts = (int_typespec *)ts;
          ranges = bts->Ranges();
          break;
        }
        case uhdmlogic_typespec: {
          logic_typespec *bts = (logic_typespec *)ts;
          ranges = bts->Ranges();
          break;
        }
        case uhdmarray_typespec: {
          array_typespec *bts = (array_typespec *)ts;
          ranges = bts->Ranges();
          break;
        }
        case uhdmpacked_array_typespec: {
          packed_array_typespec *bts = (packed_array_typespec *)ts;
          ranges = bts->Ranges();
          break;
        }
        default:
          break;
      }
    }
    if (ranges) {
      range *r = ranges->at(0);
      expr *lr = r->Left_expr();
      expr *rr = r->Right_expr();
      bool invalidValue = false;
      lr = reduceExpr(lr, invalidValue, component, compileDesign, instance,
                      BadPathId, 0, nullptr, true);
      UHDM::ExprEval eval;
      int64_t lrv = eval.get_value(invalidValue, lr);
      rr = reduceExpr(rr, invalidValue, component, compileDesign, instance,
                      BadPathId, 0, nullptr, true);
      int64_t rrv = eval.get_value(invalidValue, rr);
      if (name == "left") {
        return lr;
      } else if (name == "right") {
        return rr;
      } else if (name == "high") {
        if (lrv > rrv) {
          return lr;
        } else {
          return rr;
        }
      } else if (name == "low") {
        if (lrv > rrv) {
          return rr;
        } else {
          return lr;
        }
      }
    }
  }
  UHDM::sys_func_call *sys = s.MakeSys_func_call();
  sys->VpiName(StrCat("$", name));
  sys->VpiParent(pexpr);
  if (VectorOfany *arguments = compileTfCallArguments(
          component, fC, List_of_arguments, compileDesign, reduce, sys,
          instance, muteErrors)) {
    sys->Tf_call_args(arguments);
  }
  result = sys;
  return result;
}

UHDM::any *CompileHelper::compileClog2(
    DesignComponent *component, const FileContent *fC, NodeId List_of_arguments,
    CompileDesign *compileDesign, Reduce reduce, UHDM::any *pexpr,
    ValuedComponentI *instance, bool muteErrors) {
  UHDM::Serializer &s = compileDesign->getSerializer();
  UHDM::any *result = nullptr;
  NodeId Expression = List_of_arguments;
  if (fC->Type(Expression) == VObjectType::paList_of_arguments) {
    Expression = fC->Child(Expression);
  }

  bool invalidValue = false;
  int64_t val = 0;
  if (reduce == Reduce::Yes) {
    expr *operand =
        (expr *)compileExpression(component, fC, Expression, compileDesign,
                                  reduce, pexpr, instance, muteErrors);
    UHDM::ExprEval eval;
    val = eval.get_value(
        invalidValue,
        reduceExpr(operand, invalidValue, component, compileDesign, instance,
                   fC->getFileId(), fC->Line(Expression), pexpr, muteErrors));
  }
  if ((reduce == Reduce::Yes) && (invalidValue == false)) {
    val = val - 1;
    uint64_t clog2 = 0;
    for (; val > 0; clog2 = clog2 + 1) {
      val = val >> 1;
    }
    UHDM::constant *c = s.MakeConstant();
    c->VpiValue("UINT:" + std::to_string(clog2));
    c->VpiDecompile(std::to_string(clog2));
    c->VpiConstType(vpiUIntConst);
    c->VpiSize(64);
    result = c;
  } else {
    UHDM::sys_func_call *sys = s.MakeSys_func_call();
    sys->VpiName("$clog2");
    sys->VpiParent(pexpr);
    if (VectorOfany *arguments = compileTfCallArguments(
            component, fC, List_of_arguments, compileDesign, reduce, sys,
            instance, muteErrors)) {
      sys->Tf_call_args(arguments);
    }
    result = sys;
  }
  return result;
}

UHDM::any *CompileHelper::compileComplexFuncCall(
    DesignComponent *component, const FileContent *fC, NodeId name,
    CompileDesign *compileDesign, Reduce reduce, UHDM::any *pexpr,
    ValuedComponentI *instance, bool muteErrors) {
  UHDM::Serializer &s = compileDesign->getSerializer();
  UHDM::any *result = nullptr;
  NodeId dotedName = fC->Sibling(name);

  bool hierPath = false;
  NodeId tmp = dotedName;
  while (fC->Type(tmp) == VObjectType::paAttribute_instance) {
    tmp = fC->Sibling(tmp);
    dotedName = tmp;
  }
  NodeId List_of_arguments;
  while (tmp) {
    if (fC->Type(tmp) == VObjectType::slStringConst ||
        fC->Type(tmp) == VObjectType::paMethod_call_body ||
        fC->Type(tmp) == VObjectType::paSubroutine_call) {
      hierPath = true;
    } else if (fC->Type(tmp) == VObjectType::paList_of_arguments) {
      List_of_arguments = tmp;
    }
    tmp = fC->Sibling(tmp);
  }

  if (fC->Type(name) == VObjectType::paDollar_root_keyword) {
    hier_path *path = s.MakeHier_path();
    path->VpiParent(pexpr);
    VectorOfany *elems = s.MakeAnyVec();
    path->Path_elems(elems);
    NodeId Dollar_root_keyword = name;
    NodeId nameId = fC->Sibling(Dollar_root_keyword);
    ref_obj *ref = s.MakeRef_obj();
    elems->push_back(ref);
    ref->VpiName("$root");
    ref->VpiFullName("$root");
    ref->VpiParent(path);
    fC->populateCoreMembers(nameId, nameId, ref);

    std::string name = StrCat("$root.", fC->SymName(nameId));
    ref = s.MakeRef_obj();
    elems->push_back(ref);
    ref->VpiName(fC->SymName(nameId));
    ref->VpiFullName(fC->SymName(nameId));
    ref->VpiParent(path);
    fC->populateCoreMembers(nameId, nameId, ref);

    nameId = fC->Sibling(nameId);
    while (nameId) {
      if (fC->Type(nameId) == VObjectType::slStringConst) {
        name.append(".").append(fC->SymName(nameId));
        ref = s.MakeRef_obj();
        elems->push_back(ref);
        ref->VpiName(fC->SymName(nameId));
        ref->VpiFullName(fC->SymName(nameId));
        ref->VpiParent(path);
        fC->populateCoreMembers(nameId, nameId, ref);
      } else if (fC->Type(nameId) == VObjectType::paConstant_expression) {
        NodeId Constant_expresion = fC->Child(nameId);
        if (Constant_expresion) {
          bit_select *sel = s.MakeBit_select();
          sel->VpiParent(path);
          fC->populateCoreMembers(Constant_expresion, Constant_expresion, sel);
          if (expr *select = (expr *)compileExpression(
                  component, fC, Constant_expresion, compileDesign, reduce, sel,
                  instance, muteErrors)) {
            std::string bsname = decompileHelper(select);
            name += bsname;
            sel->VpiName(bsname);
            sel->VpiIndex(select);
          }
          elems->push_back(sel);
        }
      } else {
        break;
      }
      nameId = fC->Sibling(nameId);
    }
    path->VpiName(name);
    path->VpiParent(pexpr);
    result = path;
  } else if (fC->Type(name) == VObjectType::paDollar_keyword) {
    NodeId Dollar_keyword = name;
    NodeId nameId = fC->Sibling(Dollar_keyword);
    const std::string_view name = fC->SymName(nameId);
    if (name == "bits") {
      NodeId List_of_arguments = fC->Sibling(nameId);
      result = compileBits(component, fC, List_of_arguments, compileDesign,
                           reduce, pexpr, instance, false, muteErrors);
    } else if (name == "size") {
      NodeId List_of_arguments = fC->Sibling(nameId);
      result = compileBits(component, fC, List_of_arguments, compileDesign,
                           reduce, pexpr, instance, true, muteErrors);
    } else if (name == "clog2") {
      NodeId List_of_arguments = fC->Sibling(nameId);
      result = compileClog2(component, fC, List_of_arguments, compileDesign,
                            reduce, pexpr, instance, muteErrors);
    } else if (name == "high" || name == "low" || name == "left" ||
               name == "right") {
      result = compileBound(component, fC, List_of_arguments, compileDesign,
                            reduce, pexpr, instance, muteErrors, name);
    }
    if (result == nullptr) {
      NodeId List_of_arguments = fC->Sibling(nameId);
      UHDM::sys_func_call *sys = s.MakeSys_func_call();
      sys->VpiName(StrCat("$", name));
      sys->VpiParent(pexpr);
      if (VectorOfany *arguments = compileTfCallArguments(
              component, fC, List_of_arguments, compileDesign, reduce, sys,
              instance, muteErrors)) {
        sys->Tf_call_args(arguments);
      }
      result = sys;
    }
  } else if (fC->Type(name) == VObjectType::paImplicit_class_handle) {
    NodeId Handle = fC->Child(name);
    NodeId Method = fC->Sibling(name);
    if (!Method) {
      return compileExpression(component, fC, Handle, compileDesign, reduce,
                               pexpr, instance, muteErrors);
    }
    std::string_view rootName = fC->SymName(Method);
    if (fC->Type(Handle) == VObjectType::paThis_keyword) {
      rootName = "this";
    } else if (fC->Type(Handle) == VObjectType::paSuper_keyword) {
      rootName = "super";
    } else if (fC->Type(Handle) == VObjectType::paThis_dot_super) {
      rootName = "super";
    }
    NodeId List_of_arguments = fC->Sibling(Method);
    if (fC->Type(List_of_arguments) == VObjectType::paList_of_arguments) {
      method_func_call *fcall = s.MakeMethod_func_call();
      expr *object =
          (expr *)compileExpression(component, fC, Handle, compileDesign,
                                    reduce, fcall, instance, muteErrors);
      fcall->Prefix(object);
      fcall->VpiParent(pexpr);
      const std::string_view methodName = fC->SymName(Method);
      fcall->VpiName(methodName);
      fC->populateCoreMembers(Method, Method, fcall);
      if (VectorOfany *arguments = compileTfCallArguments(
              component, fC, List_of_arguments, compileDesign, reduce, fcall,
              instance, muteErrors)) {
        fcall->Tf_call_args(arguments);
      }
      result = fcall;
    } else if (fC->Type(List_of_arguments) ==
                   VObjectType::paConstant_expression ||
               fC->Type(List_of_arguments) == VObjectType::paSelect ||
               fC->Type(List_of_arguments) == VObjectType::paConstant_select) {
      // TODO: prefix the var_select with "this" class var
      // (this.fields[idx-1].get...)
      if (fC->Type(List_of_arguments) == VObjectType::paSelect)
        List_of_arguments = fC->Child(List_of_arguments);
      result = compileSelectExpression(component, fC, Method, rootName,
                                       compileDesign, reduce, pexpr, instance,
                                       muteErrors);
      if (result == nullptr) {
        hier_path *path = s.MakeHier_path();
        VectorOfany *elems = s.MakeAnyVec();
        path->Path_elems(elems);
        std::string fullName;
        ref_obj *r1 = s.MakeRef_obj();
        r1->VpiName(rootName);
        fullName = rootName;
        elems->push_back(r1);
        r1->VpiParent(path);
        fC->populateCoreMembers(Method, Method, r1);
        while (Method) {
          ref_obj *r = s.MakeRef_obj();
          NodeId nameId = Method;
          if (fC->Type(nameId) ==
              VObjectType::paPs_or_hierarchical_identifier) {
            nameId = fC->Child(Method);
          }
          r->VpiName(fC->SymName(nameId));
          r->VpiParent(path);
          fullName.append(".").append(fC->SymName(nameId));
          elems->push_back(r);
          fC->populateCoreMembers(nameId, nameId, r);

          Method = fC->Sibling(Method);
          if (fC->Type(Method) != VObjectType::slStringConst) {
            break;
          }
        }
        path->VpiName(fullName);
        result = path;
      }
    } else if (fC->Type(List_of_arguments) ==
               VObjectType::paConstant_bit_select) {
      // TODO: Fill this
      method_func_call *fcall = s.MakeMethod_func_call();
      if (expr *object =
              (expr *)compileExpression(component, fC, Handle, compileDesign,
                                        reduce, pexpr, instance, muteErrors)) {
        // TODO: make name part of the prefix, get vpiName from sibling
        fcall->Prefix(object);
      }
      if (VectorOfany *arguments = compileTfCallArguments(
              component, fC, fC->Sibling(fC->Sibling(List_of_arguments)),
              compileDesign, reduce, fcall, instance, muteErrors)) {
        fcall->Tf_call_args(arguments);
      }
      fcall->VpiName(rootName);
      fC->populateCoreMembers(Method, Method, fcall);
      result = fcall;
    } else if (fC->Type(List_of_arguments) == VObjectType::slStringConst) {
      // TODO: this is a mockup
      constant *cvar = s.MakeConstant();
      cvar->VpiDecompile("this");
      result = cvar;
    }
  } else if (fC->Type(name) == VObjectType::paClass_scope) {
    NodeId Class_type = fC->Child(name);
    NodeId Class_type_name = fC->Child(Class_type);
    NodeId Class_scope_name = fC->Sibling(name);
    NodeId List_of_arguments = fC->Sibling(Class_scope_name);
    NodeId Bit_Select;
    if (List_of_arguments) {
      if (fC->Type(List_of_arguments) == VObjectType::paSelect) {
        Bit_Select = fC->Child(List_of_arguments);
        if (!fC->Child(Bit_Select)) {
          List_of_arguments = InvalidNodeId;
        }
      }
    }

    const std::string_view packagename = fC->SymName(Class_type_name);
    const std::string_view functionname = fC->SymName(Class_scope_name);
    std::string basename = StrCat(packagename, "::", functionname);
    tf_call *call = nullptr;
    std::pair<task_func *, DesignComponent *> ret =
        getTaskFunc(basename, component, compileDesign, instance, pexpr);
    task_func *tf = ret.first;
    if (tf) {
      if (tf->UhdmType() == uhdmfunction) {
        func_call *fcall = s.MakeFunc_call();
        fcall->Function(any_cast<function *>(tf));
        call = fcall;
      } else {
        task_call *tcall = s.MakeTask_call();
        tcall->Task(any_cast<task *>(tf));
        call = tcall;
      }
      tf->VpiParent(call);
      call->VpiParent(pexpr);
      fC->populateCoreMembers(Class_type_name, Class_type_name, call);
    }
    Design *design = compileDesign->getCompiler()->getDesign();
    Package *pack = design->getPackage(packagename);
    if (call == nullptr) {
      if (pack && !List_of_arguments) {
        Value *val = pack->getValue(functionname);
        if (val && val->isValid()) {
          if (Bit_Select) {
            if (fC->Type(Bit_Select) == VObjectType::paConstant_select) {
              Bit_Select = fC->Child(Bit_Select);
            }
            if (any *tmpResult = compileSelectExpression(
                    component, fC, Bit_Select, basename, compileDesign, reduce,
                    pexpr, instance, muteErrors)) {
              return tmpResult;
            }
          }
          UHDM::constant *c = s.MakeConstant();
          c->VpiValue(val->uhdmValue());
          c->VpiDecompile(val->decompiledValue());
          c->VpiSize(val->getSize());
          c->VpiConstType(val->vpiValType());
          result = c;
          return result;
        }
      }
    }
    if (call == nullptr) {
      if (pack && pack->getParameters()) {
        for (UHDM::any *param : *pack->getParameters()) {
          if (param->VpiName() == functionname) {
            if ((fC->Type(List_of_arguments) == VObjectType::paSelect) &&
                (fC->Child(List_of_arguments))) {
              result = compileSelectExpression(
                  component, fC, fC->Child(List_of_arguments),
                  StrCat(packagename, "::", functionname), compileDesign,
                  reduce, pexpr, instance, muteErrors);
              if (result)
                result->VpiParent(param);
              else
                result = param;
            } else if ((fC->Type(List_of_arguments) ==
                        VObjectType::slStringConst)) {
              hier_path *path = s.MakeHier_path();
              VectorOfany *elems = s.MakeAnyVec();
              path->Path_elems(elems);
              ref_obj *ref = s.MakeRef_obj();
              ref->VpiName(StrCat(packagename, "::", functionname));
              ref->VpiFullName(StrCat(packagename, "::", functionname));
              ref->Actual_group(param);
              ref->VpiParent(path);
              fC->populateCoreMembers(name, name, ref);
              elems->push_back(ref);
              while (List_of_arguments) {
                if ((fC->Type(List_of_arguments) ==
                     VObjectType::slStringConst)) {
                  ref_obj *ref = s.MakeRef_obj();
                  ref->VpiName(fC->SymName(List_of_arguments));
                  ref->VpiParent(path);
                  fC->populateCoreMembers(List_of_arguments, List_of_arguments,
                                          ref);
                  elems->push_back(ref);
                }
                List_of_arguments = fC->Sibling(List_of_arguments);
              }
              result = path;
            } else {
              ref_obj *ref = s.MakeRef_obj();
              ref->VpiName(StrCat(packagename, "::", functionname));
              ref->VpiFullName(StrCat(packagename, "::", functionname));
              ref->Actual_group(param);
              ref->VpiParent(pexpr);
              fC->populateCoreMembers(name, name, ref);
              result = ref;
            }
            break;
          }
        }
        if (result) return result;
      }
    }
    if (call != nullptr) {
      call->VpiName(basename);
      if (VectorOfany *arguments = compileTfCallArguments(
              component, fC, List_of_arguments, compileDesign, reduce, call,
              instance, muteErrors)) {
        call->Tf_call_args(arguments);
      }
      result = call;
    } else {
      result = compileExpression(component, fC, name, compileDesign, reduce,
                                 pexpr, instance, muteErrors);
    }
  } else if (fC->Type(dotedName) == VObjectType::paSelect ||
             fC->Type(dotedName) == VObjectType::paConstant_select ||
             fC->Type(dotedName) == VObjectType::paConstant_expression ||
             fC->Type(dotedName) == VObjectType::slStringConst ||
             fC->Type(dotedName) == VObjectType::paConstant_bit_select ||
             fC->Type(dotedName) == VObjectType::paBit_select) {
    NodeId Bit_select = fC->Child(dotedName);
    const std::string_view sval = fC->SymName(name);
    NodeId selectName = fC->Sibling(dotedName);
    if (!selectName) {
      if (NodeId c = fC->Child(dotedName)) {
        if (NodeId s = fC->Sibling(c)) {
          selectName = s;
        }
      }
    }

    if (dotedName) {
      std::string the_name(fC->SymName(name));
      if (!hierPath) {
        VObjectType dtype = fC->Type(dotedName);
        VObjectType selectType = fC->Type(selectName);
        if (selectName &&
            (selectType == VObjectType::paConstant_part_select_range)) {
          result = compileSelectExpression(component, fC, dotedName, "",
                                           compileDesign, reduce, pexpr,
                                           instance, muteErrors);
          if (result && (result->UhdmType() == UHDM::uhdmvar_select)) {
            fC->populateCoreMembers(name, dotedName, result);
            ((var_select *)result)->VpiName(sval);
          }
          return result;
        } else if (Bit_select &&
                   (fC->Child(Bit_select) || fC->Sibling(Bit_select))) {
          result = compileSelectExpression(component, fC, Bit_select, sval,
                                           compileDesign, reduce, pexpr,
                                           instance, muteErrors);
          if (result && (result->UhdmType() == UHDM::uhdmpart_select)) {
            fC->populateCoreMembers(name, dotedName, result);
          }
          return result;
        } else if ((!selectName) &&
                   (dtype == VObjectType::paSelect ||
                    dtype == VObjectType::paConstant_bit_select ||
                    dtype == VObjectType::paBit_select ||
                    dtype == VObjectType::paConstant_select)) {
          std::string ind;
          expr *index = nullptr;
          if (NodeId Expression = fC->Child(Bit_select)) {
            index = (expr *)compileExpression(component, fC, Expression,
                                              compileDesign, Reduce::No, pexpr,
                                              instance);
          }
          if (index) {
            bit_select *select = s.MakeBit_select();
            index->VpiParent(select);
            select->VpiIndex(index);
            the_name += "[" + decompileHelper(index) + "]";
            select->VpiFullName(the_name);
            select->VpiName(fC->SymName(name));
            result = select;
          } else {
            ref_obj *ref = s.MakeRef_obj();
            ref->VpiName(the_name);
            ref->VpiFullName(the_name);
            result = ref;
            fC->populateCoreMembers(name, name, ref);
          }
          result->VpiParent(pexpr);
          fC->populateCoreMembers(name, name, result);
          return result;
        }
      }

      UHDM::hier_path *path = s.MakeHier_path();
      VectorOfany *elems = s.MakeAnyVec();
      if (instance && (reduce == Reduce::Yes)) {
        UHDM::any *rootValue =
            getObject(the_name, component, compileDesign, instance, pexpr);
        if (rootValue) {
          if (expr *expval = any_cast<expr *>(rootValue)) {
            path->Root_value(rootValue);
            if (ref_typespec *expval_rt = expval->Typespec()) {
              if (path->Typespec() == nullptr) {
                ref_typespec *path_rt = s.MakeRef_typespec();
                path_rt->VpiParent(path);
                path->Typespec(path_rt);
              }
              path->Typespec()->Actual_typespec(expval_rt->Actual_typespec());
            }
          } else if (UHDM::port *expval = any_cast<port *>(rootValue)) {
            path->Root_value(expval->Low_conn());
          } else if (UHDM::param_assign *passign =
                         any_cast<param_assign *>(rootValue)) {
            path->Root_value(passign->Rhs());
            const any *param = passign->Lhs();
            typespec *tps = nullptr;
            if (param->UhdmType() == uhdmparameter) {
              parameter *p = (parameter *)param;
              if (UHDM::ref_typespec *rt = p->Typespec()) {
                tps = rt->Actual_typespec();
              }
            } else {
              type_parameter *p = (type_parameter *)param;
              if (UHDM::ref_typespec *rt = p->Typespec()) {
                tps = rt->Actual_typespec();
              }
            }
            if (path->Typespec() == nullptr) {
              ref_typespec *rt = s.MakeRef_typespec();
              rt->VpiParent(path);
              path->Typespec(rt);
            }
            path->Typespec()->Actual_typespec(tps);
          }
        }
      }
      std::string tmpName = the_name;
      path->Path_elems(elems);
      bool is_hierarchical = false;
      while (dotedName) {
        VObjectType dtype = fC->Type(dotedName);
        NodeId BitSelect = fC->Child(dotedName);
        if (dtype == VObjectType::slStringConst) {
          the_name.append(".").append(fC->SymName(dotedName));
          if (!tmpName.empty()) {
            ref_obj *ref = s.MakeRef_obj();
            elems->push_back(ref);
            ref->VpiName(tmpName);
            ref->VpiFullName(tmpName);
            ref->VpiParent(path);
            fC->populateCoreMembers(name, name, ref);
            tmpName.clear();
            is_hierarchical = true;
          }
          tmpName = fC->SymName(dotedName);
        } else if (dtype == VObjectType::paSelect ||
                   dtype == VObjectType::paBit_select ||
                   dtype == VObjectType::paConstant_bit_select ||
                   dtype == VObjectType::paConstant_expression) {
          std::string ind;
          while (BitSelect) {
            is_hierarchical = true;
            NodeId Expression = fC->Child(BitSelect);
            if (!Expression) {
              if (BitSelect) {
                Expression = fC->Sibling(BitSelect);
                if (Expression) {
                  BitSelect = Expression;
                  Expression = fC->Child(BitSelect);
                }
              }
            }
            if (dtype == VObjectType::paConstant_expression) {
              Expression = dotedName;
            }
            if ((fC->Type(BitSelect) == VObjectType::paBit_select) &&
                fC->Child(BitSelect)) {
              if (expr *select = (expr *)compileSelectExpression(
                      component, fC, BitSelect, tmpName, compileDesign, reduce,
                      path, instance, muteErrors)) {
                if ((select->UhdmType() == UHDM::uhdmpart_select) ||
                    (select->UhdmType() == UHDM::uhdmvar_select)) {
                  fC->populateCoreMembers(name, dotedName, select);
                }
                elems->push_back(select);
                the_name += decompileHelper(select);
                tmpName.clear();
              }
              break;
            } else if (fC->Type(BitSelect) ==
                       VObjectType::paPart_select_range) {
              if (expr *select = (expr *)compilePartSelectRange(
                      component, fC, Expression, "CREATE_UNNAMED_PARENT",
                      compileDesign, reduce, path, instance, muteErrors)) {
                the_name += decompileHelper(select);
                // Fix start/end to include the name
                select->VpiColumnNo(fC->Column(name));
                if (ref_obj *ro = any_cast<ref_obj *>(select)) {
                  ro->VpiName(tmpName);
                  ro->VpiFullName(the_name);
                }
                elems->push_back(select);
              }
            } else if (Expression &&
                       (fC->Type(Expression) ==
                        VObjectType::paPart_select_range) &&
                       fC->Child(Expression)) {
              if (expr *select = (expr *)compilePartSelectRange(
                      component, fC, fC->Child(Expression),
                      "CREATE_UNNAMED_PARENT", compileDesign, reduce, path,
                      instance, muteErrors)) {
                the_name += decompileHelper(select);
                // Fix start/end to include the name
                select->VpiColumnNo(fC->Column(name));
                if (ref_obj *ro = any_cast<ref_obj *>(select)) {
                  ro->VpiName(tmpName);
                  ro->VpiFullName(the_name);
                }
                elems->push_back(select);
              }
            } else if (Expression) {
              if (expr *index = (expr *)compileExpression(
                      component, fC, Expression, compileDesign, reduce, path,
                      instance, muteErrors)) {
                the_name += "[" + decompileHelper(index) + "]";
                bit_select *select = s.MakeBit_select();
                select->VpiName(tmpName);
                select->VpiFullName(the_name);
                select->VpiIndex(index);
                select->VpiParent(path);
                fC->populateCoreMembers(name, name, select);
                elems->push_back(select);
              }
            } else {
              ref_obj *ref = s.MakeRef_obj();
              elems->push_back(ref);
              ref->VpiName(tmpName);
              ref->VpiParent(path);
              fC->populateCoreMembers(name, name, ref);
            }
            tmpName.clear();
            if (dtype == VObjectType::paSelect)
              BitSelect = fC->Sibling(BitSelect);
            else
              break;
          }
        }

        NodeId lookAhead = fC->Sibling(dotedName);

        if ((fC->Type(dotedName) == VObjectType::paMethod_call_body) ||
            (fC->Type(lookAhead) == VObjectType::paList_of_arguments)) {
          NodeId method_child = fC->Child(dotedName);
          method_func_call *fcall = nullptr;
          if (fC->Type(method_child) == VObjectType::paBuilt_in_method_call) {
            // vpiName: method name (Array_method_name above)
            NodeId method_name_node = fC->Child(method_child);
            if (method_name_node)
              method_name_node = fC->Child(method_name_node);
            if (method_name_node)
              method_name_node = fC->Child(method_name_node);

            std::string method_name;
            if (method_name_node) {
              method_name = fC->SymName(method_name_node);
              VObjectType calltype = fC->Type(method_name_node);
              if (calltype == VObjectType::paAnd_call) {
                method_name = "and";
              } else if (calltype == VObjectType::paOr_call) {
                method_name = "or";
              } else if (calltype == VObjectType::paXor_call) {
                method_name = "xor";
              } else if (calltype == VObjectType::paUnique_call) {
                method_name = "unique";
              }
            }

            NodeId randomize_call = fC->Child(method_child);

            if (fC->Type(randomize_call) == VObjectType::paRandomize_call) {
              fcall =
                  compileRandomizeCall(component, fC, fC->Child(randomize_call),
                                       compileDesign, pexpr);
            } else {
              fcall = s.MakeMethod_func_call();
              fcall->VpiName(method_name);
              fC->populateCoreMembers(method_name_node, method_name_node,
                                      fcall);
              NodeId list_of_arguments =
                  fC->Sibling(fC->Child(fC->Child(method_child)));
              NodeId with_conditions_node;
              if (fC->Type(list_of_arguments) ==
                  VObjectType::paList_of_arguments) {
                if (VectorOfany *arguments = compileTfCallArguments(
                        component, fC, list_of_arguments, compileDesign, reduce,
                        fcall, instance, muteErrors)) {
                  fcall->Tf_call_args(arguments);
                }
                with_conditions_node = fC->Sibling(list_of_arguments);
              } else {
                with_conditions_node = list_of_arguments;
              }
              // vpiWith: with conditions (expression in node u<62> above)
              // (not in every method, node id is 0 if missing)
              if (with_conditions_node) {
                if (expr *with_conditions = (expr *)compileExpression(
                        component, fC, with_conditions_node, compileDesign,
                        reduce, pexpr, instance, muteErrors)) {
                  fcall->With(with_conditions);
                }
              }
            }
            elems->push_back(fcall);
            tmpName.clear();
            dotedName = fC->Sibling(dotedName);
          } else {
            fcall = s.MakeMethod_func_call();
            const std::string_view methodName = fC->SymName(dotedName);
            fcall->VpiName(methodName);
            fC->populateCoreMembers(dotedName, dotedName, fcall);
            if (VectorOfany *arguments = compileTfCallArguments(
                    component, fC, List_of_arguments, compileDesign, reduce,
                    fcall, instance, muteErrors)) {
              fcall->Tf_call_args(arguments);
            }
            elems->push_back(fcall);
            tmpName.clear();
            dotedName = fC->Sibling(dotedName);
          }
          if (fcall != nullptr) fcall->VpiParent(path);
        }
        name = dotedName;
        if (dotedName) dotedName = fC->Sibling(dotedName);
      }
      if (is_hierarchical) {
        if (!tmpName.empty()) {
          ref_obj *ref = s.MakeRef_obj();
          elems->push_back(ref);
          ref->VpiName(tmpName);
          ref->VpiFullName(the_name);
          ref->VpiParent(path);
          fC->populateCoreMembers(name, name, ref);
          tmpName.clear();
        }
        path->VpiName(the_name);
        path->VpiFullName(the_name);
        path->VpiParent(pexpr);

        if (elems->size() == 1) {
          result = elems->at(0);
        } else {
          result = path;
        }
      } else {
        ref_obj *ref = s.MakeRef_obj();
        ref->VpiName(tmpName);
        ref->VpiParent(pexpr);
        fC->populateCoreMembers(name, name, ref);
        tmpName.clear();
        result = ref;
      }
    } else if (UHDM::any *st = getValue(
                   sval, component, compileDesign, reduce, instance,
                   fC->getFileId(), fC->Line(Bit_select), pexpr, muteErrors)) {
      UHDM_OBJECT_TYPE type = st->UhdmType();
      NodeId Select = dotedName;
      if (NodeId BitSelect = fC->Child(Select)) {
        NodeId Expression = fC->Child(BitSelect);
        while (Expression) {
          expr *index = (expr *)compileExpression(component, fC, Expression,
                                                  compileDesign, reduce, pexpr,
                                                  instance, muteErrors);
          if (index && index->UhdmType() == uhdmconstant) {
            bool invalidValue = false;
            UHDM::ExprEval eval;
            uint64_t ind = (uint64_t)eval.get_value(invalidValue, index);
            if (invalidValue == false && type == uhdmoperation) {
              operation *op = (operation *)st;
              int32_t opType = op->VpiOpType();
              if (opType == vpiAssignmentPatternOp) {
                VectorOfany *operands = op->Operands();
                if (ind < operands->size()) {
                  result = operands->at(ind);
                  st = result;
                }
              } else if (opType == vpiConcatOp) {
                VectorOfany *operands = op->Operands();
                if (ind < operands->size()) {
                  result = operands->at(ind);
                  st = result;
                }
              }
            }
          }
          Expression = fC->Sibling(Expression);
        }
      }
      if (result == nullptr) {
        result = compileSelectExpression(component, fC, Bit_select, sval,
                                         compileDesign, reduce, pexpr, instance,
                                         muteErrors);
      }
    } else {
      result = compileSelectExpression(component, fC, Bit_select, sval,
                                       compileDesign, reduce, pexpr, instance,
                                       muteErrors);
    }
    if (result == nullptr) {
      const std::string_view n = fC->SymName(name);
      ref_obj *ref = s.MakeRef_obj();
      ref->VpiName(n);
      ref->VpiParent(pexpr);
      if (pexpr) {
        if (UHDM::any *var = bindVariable(component, pexpr, n, compileDesign))
          ref->Actual_group(var);
        else if (component)
          component->needLateBinding(ref);
      } else if (instance) {
        if (UHDM::any *var =
                bindVariable(component, instance, n, compileDesign))
          ref->Actual_group(var);
        else if (component)
          component->needLateBinding(ref);
      } else if (component) {
        component->needLateBinding(ref);
      }
      result = ref;
    }
  } else if (fC->Type(dotedName) == VObjectType::paList_of_arguments) {
    result =
        compileTfCall(component, fC, fC->Parent(name), compileDesign, pexpr);
  } else if (fC->Type(name) == VObjectType::slStringConst) {
    const std::string_view n = fC->SymName(name);
    ref_obj *ref = s.MakeRef_obj();
    ref->VpiName(n);
    ref->VpiParent(pexpr);
    if (pexpr) {
      if (UHDM::any *var = bindVariable(component, pexpr, n, compileDesign))
        ref->Actual_group(var);
      else if (component)
        component->needLateBinding(ref);
    } else if (instance) {
      if (UHDM::any *var = bindVariable(component, instance, n, compileDesign))
        ref->Actual_group(var);
      else if (component)
        component->needLateBinding(ref);
    } else if (component) {
      component->needLateBinding(ref);
    }
    result = ref;
  } else if (fC->Type(name) == VObjectType::paSubroutine_call) {
    result = compileExpression(component, fC, fC->Parent(name), compileDesign,
                               reduce, pexpr, instance, muteErrors);
  } else if (!dotedName) {
    const std::string_view the_name = fC->SymName(name);
    ref_obj *ref = s.MakeRef_obj();
    ref->VpiName(the_name);
    ref->VpiFullName(the_name);
    ref->VpiParent(pexpr);
    fC->populateCoreMembers(name, name, ref);
    result = ref;
  }
  return result;
}

bool CompileHelper::parseConstant(const UHDM::constant &constant,
                                  int64_t *value) {
  std::string_view v = constant.VpiValue();
  if (v.length() <= 4) return false;  // All prefices are at least this long.

  switch (constant.VpiConstType()) {
    case vpiBinaryConst: {
      v.remove_prefix(std::string_view("BIN:").length());
      return NumUtils::parseBinary(v, value) != nullptr;
    }
    case vpiDecConst: {
      v.remove_prefix(std::string_view("DEC:").length());
      return NumUtils::parseInt64(v, value) != nullptr;
    }
    case vpiHexConst: {
      v.remove_prefix(std::string_view("HEX:").length());
      return NumUtils::parseHex(v, value) != nullptr;
    }
    case vpiOctConst: {
      v.remove_prefix(std::string_view("OCT:").length());
      return NumUtils::parseOctal(v, value) != nullptr;
    }
    case vpiIntConst: {
      v.remove_prefix(std::string_view("INT:").length());
      return NumUtils::parseInt64(v, value) != nullptr;
    }
    case vpiUIntConst: {
      v.remove_prefix(std::string_view("UINT:").length());
      return NumUtils::parseIntLenient(v, value) != nullptr;
    }
    default: {
      if (v.find("UINT:") == 0) {
        v.remove_prefix(std::string_view("UINT:").length());
        return NumUtils::parseIntLenient(v, value) != nullptr;
      } else if (v.find("INT:") == 0) {
        v.remove_prefix(std::string_view("INT:").length());
        return NumUtils::parseInt64(v, value) != nullptr;
      }
      break;
    }
  }
  return false;
}

int64_t CompileHelper::getValue(bool &validValue, DesignComponent *component,
                                const FileContent *fC, NodeId nodeId,
                                CompileDesign *compileDesign, Reduce reduce,
                                UHDM::any *pexpr, ValuedComponentI *instance,
                                bool muteErrors) {
  int64_t result = 0;
  validValue = true;
  UHDM::any *expr = compileExpression(component, fC, nodeId, compileDesign,
                                      reduce, pexpr, instance, muteErrors);
  if (expr && expr->UhdmType() == UHDM::uhdmconstant) {
    validValue = parseConstant(*(const UHDM::constant *)expr, &result);
  } else {
    validValue = false;
  }
  return result;
}

void CompileHelper::reorderAssignmentPattern(
    DesignComponent *mod, const UHDM::any *lhs, UHDM::any *rhs,
    CompileDesign *compileDesign, ValuedComponentI *instance, uint32_t level) {
  if (rhs->UhdmType() != uhdmoperation) return;
  operation *op = (operation *)rhs;
  int32_t optype = op->VpiOpType();
  if (optype == vpiConditionOp) {
    bool invalidValue = false;
    expr *tmp = reduceExpr(op, invalidValue, mod, compileDesign, instance,
                           BadPathId, 0, nullptr, true);
    if (tmp && (tmp->UhdmType() == uhdmoperation) && (invalidValue == false)) {
      op = (operation *)tmp;
      optype = op->VpiOpType();
    }
  }
  if (op->VpiReordered()) return;
  if ((optype != vpiAssignmentPatternOp) && (optype != vpiConcatOp)) return;
  VectorOfany *operands = op->Operands();
  bool ordered = true;
  for (any *operand : *operands) {
    if (operand->UhdmType() == uhdmtagged_pattern) {
      ordered = false;
      break;
    }
  }
  if (ordered) {
    if (lhs->UhdmType() == uhdmparameter) {
      parameter *p = (parameter *)lhs;
      VectorOfrange *ranges = nullptr;
      if (p->Ranges()) {
        ranges = p->Ranges();
      } else if (const ref_typespec *rt = p->Typespec()) {
        if (const typespec *tps = rt->Actual_typespec()) {
          UHDM_OBJECT_TYPE ttype = tps->UhdmType();
          if (ttype == uhdmbit_typespec) {
            ranges = ((bit_typespec *)tps)->Ranges();
          } else if (ttype == uhdmlogic_typespec) {
            ranges = ((logic_typespec *)tps)->Ranges();
          } else if (ttype == uhdmarray_typespec) {
            ranges = ((array_typespec *)tps)->Ranges();
          } else if (ttype == uhdmpacked_array_typespec) {
            ranges = ((packed_array_typespec *)tps)->Ranges();
          }
        }
      }
      if (ranges) {
        if (level < ranges->size()) {
          range *r = ranges->at(level);
          expr *lr = r->Left_expr();
          expr *rr = r->Right_expr();
          bool invalidValue = false;
          UHDM::ExprEval eval;
          lr = reduceExpr(lr, invalidValue, mod, compileDesign, instance,
                          BadPathId, 0, nullptr, true);
          int64_t lrv = eval.get_value(invalidValue, lr);
          rr = reduceExpr(rr, invalidValue, mod, compileDesign, instance,
                          BadPathId, 0, nullptr, true);
          int64_t rrv = eval.get_value(invalidValue, rr);
          if (lrv > rrv) {
            op->VpiReordered(true);
            std::reverse(operands->begin(), operands->end());
            if (level == 0) {
              if (instance) {
                instance->setComplexValue(p->VpiName(), op);
              } else {
                mod->setComplexValue(p->VpiName(), op);
              }
            }
          }
        }
      }
    }
  }
  for (any *operand : *operands) {
    if (operand->UhdmType() == uhdmoperation) {
      reorderAssignmentPattern(mod, lhs, operand, compileDesign, instance,
                               level + 1);
    }
  }
}
}  // namespace SURELOG
