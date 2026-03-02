/*
 Copyright 2020 Alain Dargelas

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
 * File:   NetlistElaboration.cpp
 * Author: alain
 *
 * Created on Mar 1, 2020, 6:36 PM
 */

#include "Surelog/DesignCompile/NetlistElaboration.h"

#include <uhdm/BaseClass.h>
#include <uhdm/expr.h>
#include <uhdm/uhdm_types.h>

#include <algorithm>
#include <cstdint>
#include <cstdlib>
#include <map>
#include <set>
#include <string>
#include <utility>
#include <vector>

#include "Surelog/CommandLine/CommandLineParser.h"
#include "Surelog/Common/FileSystem.h"
#include "Surelog/Common/NodeId.h"
#include "Surelog/Common/PathId.h"
#include "Surelog/Design/DataType.h"
#include "Surelog/Design/DesignComponent.h"
#include "Surelog/Design/DesignElement.h"
#include "Surelog/Design/DummyType.h"
#include "Surelog/Design/Enum.h"
#include "Surelog/Design/FileContent.h"
#include "Surelog/Design/ModPort.h"
#include "Surelog/Design/ModuleDefinition.h"
#include "Surelog/Design/ModuleInstance.h"
#include "Surelog/Design/Netlist.h"
#include "Surelog/Design/ParamAssign.h"
#include "Surelog/Design/Parameter.h"
#include "Surelog/Design/SimpleType.h"
#include "Surelog/Design/Struct.h"
#include "Surelog/Design/ValuedComponentI.h"
#include "Surelog/DesignCompile/CompileDesign.h"
#include "Surelog/DesignCompile/CompileHelper.h"
#include "Surelog/DesignCompile/TestbenchElaboration.h"
#include "Surelog/DesignCompile/UhdmWriter.h"
#include "Surelog/ErrorReporting/Error.h"
#include "Surelog/ErrorReporting/ErrorDefinition.h"
#include "Surelog/ErrorReporting/Location.h"
#include "Surelog/Package/Package.h"
#include "Surelog/SourceCompile/Compiler.h"
#include "Surelog/SourceCompile/SymbolTable.h"
#include "Surelog/SourceCompile/VObjectTypes.h"
#include "Surelog/Testbench/TypeDef.h"
#include "Surelog/Utils/StringUtils.h"

// UHDM
#include <uhdm/ElaboratorListener.h>
#include <uhdm/ExprEval.h>
#include <uhdm/clone_tree.h>
#include <uhdm/sv_vpi_user.h>
#include <uhdm/uhdm.h>
#include <uhdm/vpi_user.h>

namespace SURELOG {

using namespace UHDM;  // NOLINT (using a bunch of these)

NetlistElaboration::NetlistElaboration(CompileDesign* compileDesign)
    : TestbenchElaboration(compileDesign) {
  m_exprBuilder.seterrorReporting(
      m_compileDesign->getCompiler()->getErrorContainer(),
      m_compileDesign->getCompiler()->getSymbolTable());
  m_exprBuilder.setDesign(m_compileDesign->getCompiler()->getDesign());
  m_helper.seterrorReporting(
      m_compileDesign->getCompiler()->getErrorContainer(),
      m_compileDesign->getCompiler()->getSymbolTable());
  m_symbols = m_compileDesign->getCompiler()->getSymbolTable();
  m_errors = m_compileDesign->getCompiler()->getErrorContainer();
}

NetlistElaboration::~NetlistElaboration() = default;

bool NetlistElaboration::elaboratePackages() {
  Design* design = m_compileDesign->getCompiler()->getDesign();
  // Packages
  auto& packageDefs = design->getPackageDefinitions();
  for (auto& packageDef : packageDefs) {
    Package* p = packageDef.second;
    Reduce reduce = Reduce::No;
    for (Package* pack : {p->getUnElabPackage(), p}) {
      if (pack->getNetlist() == nullptr) {
        Netlist* netlist = new Netlist(nullptr);
        pack->setNetlist(netlist);
      }
      Netlist* netlist = pack->getNetlist();
      // Variables and nets in Packages
      std::set<Signal*> notSignals;
      TypespecCache tscache;
      for (Signal* sig : pack->getSignals()) {
        if (!elabSignal(sig, nullptr, nullptr, nullptr, netlist, pack, "",
                        false, tscache, reduce)) {
          notSignals.insert(sig);
        }
      }
      for (auto sig : notSignals) {
        for (std::vector<Signal*>::iterator itr = pack->getSignals().begin();
             itr != pack->getSignals().end(); itr++) {
          if ((*itr) == sig) {
            pack->getSignals().erase(itr);
            break;
          }
        }
      }
      reduce = Reduce::Yes;
    }
  }
  return true;
}

bool NetlistElaboration::elaborateInstance(ModuleInstance* instance) {
  return elaborate_(instance, false);
}

bool NetlistElaboration::elaborate() {
  Design* design = m_compileDesign->getCompiler()->getDesign();
  elaboratePackages();

  // Top level modules
  const std::vector<ModuleInstance*>& topModules =
      design->getTopLevelModuleInstances();
  return std::all_of(
      topModules.begin(), topModules.end(),
      [this](ModuleInstance* inst) { return elaborate_(inst, true); });
}

bool NetlistElaboration::elab_parameters_(ModuleInstance* instance,
                                          bool param_port) {
  FileSystem* const fileSystem = FileSystem::getInstance();
  Serializer& s = m_compileDesign->getSerializer();
  if (!instance) return true;
  Netlist* netlist = instance->getNetlist();
  if (netlist == nullptr) return true;
  bool en_replay =
      m_compileDesign->getCompiler()->getCommandLineParser()->replay();
  ModuleDefinition* mod =
      valuedcomponenti_cast<ModuleDefinition*>(instance->getDefinition());
  VectorOfparam_assign* assigns = netlist->param_assigns();
  if (!mod) {
    if (param_port) return true;
    for (const auto& mv : instance->getMappedValues()) {
      if (assigns == nullptr) {
        netlist->param_assigns(s.MakeParam_assignVec());
        assigns = netlist->param_assigns();
      }
      const std::string& paramName = mv.first;
      Value* value = mv.second.first;
      uint32_t line = mv.second.second;
      const FileContent* instfC = instance->getFileContent();
      if (value && value->isValid()) {
        param_assign* inst_assign = s.MakeParam_assign();
        inst_assign->VpiOverriden(instance->isOverridenParam(paramName));
        parameter* p = s.MakeParameter();
        p->VpiName(paramName);
        p->VpiParent(inst_assign);
        constant* c = s.MakeConstant();
        c->VpiValue(value->uhdmValue());
        c->VpiDecompile(value->decompiledValue());
        c->VpiFile(fileSystem->toPath(instfC->getFileId()));
        c->VpiSize(value->getSize());
        c->VpiConstType(value->vpiValType());
        c->VpiLineNo(line);
        c->VpiEndLineNo(line);
        inst_assign->Lhs(p);
        inst_assign->Rhs(c);
        assigns->push_back(inst_assign);
      }
    }
    return true;
  }
  if (mod->getParameters() != nullptr) {
    // Type params
    for (const auto& nameParam : mod->getParameterMap()) {
      Parameter* sit = nameParam.second;
      elabTypeParameter_(mod, sit, instance);
    }
  }
  // Regular
  bool isMultidimensional = false;
  for (ParamAssign* assign : mod->getParamAssignVec()) {
    if (param_port ^ assign->isPortParam()) {
      continue;
    }
    if (assigns == nullptr) {
      netlist->param_assigns(s.MakeParam_assignVec());
      assigns = netlist->param_assigns();
    }
    param_assign* mod_assign = assign->getUhdmParamAssign();
    isMultidimensional = assign->isMultidimensional();
    const std::string_view paramName =
        assign->getFileContent()->SymName(assign->getParamId());
    if (mod_assign) {
      const any* rhs = mod_assign->Rhs();
      expr* complexVal = instance->getComplexValue(paramName);
      if (complexVal) {
        rhs = complexVal;
      }
      bool isOverriden = instance->isOverridenParam(paramName);
      if ((!isOverriden) || complexVal) {
        // Complex value(default or overriden), no simple value
        if (rhs && rhs->UhdmType() == uhdmoperation) {
          operation* op = (operation*)rhs;
          int32_t opType = op->VpiOpType();
          if (opType == vpiCastOp || (opType == vpiMultiConcatOp) ||
              (opType == vpiConditionOp)) {
            isMultidimensional = false;
          }

          // Don't reduce these operations
          if (opType == vpiAssignmentPatternOp ||
              opType == vpiMultiAssignmentPatternOp) {
            ElaboratorContext elaboratorContext(&s, false, true);
            param_assign* pclone =
                (param_assign*)UHDM::clone_tree(mod_assign, &elaboratorContext);
            pclone->VpiParent((any*)mod_assign->VpiParent());
            pclone->VpiOverriden(instance->isOverridenParam(paramName));
            const any* lhs = pclone->Lhs();
            any* rhs = pclone->Rhs();
            if (complexVal) {
              rhs = UHDM::clone_tree(complexVal, &elaboratorContext);
              rhs->VpiParent(pclone);
            }
            const typespec* ts = nullptr;
            if (lhs->UhdmType() == uhdmparameter) {
              if (const ref_typespec* rt = ((parameter*)lhs)->Typespec()) {
                ts = rt->Actual_typespec();
              }
            }
            if (m_helper.substituteAssignedValue(rhs, m_compileDesign)) {
              rhs = m_helper.expandPatternAssignment(ts, (expr*)rhs, mod,
                                                     m_compileDesign, instance);
            }
            rhs = (expr*)m_helper.defaultPatternAssignment(
                ts, rhs, mod, m_compileDesign, instance);
            pclone->Rhs(rhs);
            m_helper.reorderAssignmentPattern(mod, lhs, rhs, m_compileDesign,
                                              instance, 0);

            if (lhs->UhdmType() == uhdmparameter) {
              parameter* p = (parameter*)lhs;
              const typespec* tps = nullptr;
              if (const ref_typespec* rt = p->Typespec()) {
                tps = rt->Actual_typespec();
              }
              if (tps) {
                UHDM::ExprEval eval;
                if (expr* tmp =
                        eval.flattenPatternAssignments(s, tps, (expr*)rhs)) {
                  if (tmp->UhdmType() == uhdmoperation) {
                    ((operation*)rhs)->Operands(((operation*)tmp)->Operands());
                  }
                }
              } else if (rhs->UhdmType() == uhdmoperation) {
                operation* op = (operation*)rhs;
                if (const ref_typespec* rt = op->Typespec()) {
                  if (const typespec* tps = rt->Actual_typespec()) {
                    UHDM::ExprEval eval;
                    if (expr* tmp = eval.flattenPatternAssignments(
                            s, tps, (expr*)rhs)) {
                      if (tmp->UhdmType() == uhdmoperation) {
                        ((operation*)rhs)
                            ->Operands(((operation*)tmp)->Operands());
                      }
                    }
                  }
                }
              }
            }
            assigns->push_back(pclone);
            continue;
          }
        }
      }
    }

    param_assign* inst_assign = s.MakeParam_assign();
    inst_assign->VpiOverriden(instance->isOverridenParam(paramName));
    inst_assign->VpiFile(mod_assign->VpiFile());
    inst_assign->VpiLineNo(mod_assign->VpiLineNo());
    inst_assign->VpiColumnNo(mod_assign->VpiColumnNo());
    inst_assign->VpiEndLineNo(mod_assign->VpiEndLineNo());
    inst_assign->VpiEndColumnNo(mod_assign->VpiEndColumnNo());
    inst_assign->Lhs(mod_assign->Lhs());

    bool overriden = false;
    for (Parameter* tpm :
         instance->getTypeParams()) {  // for parameters that do not resolve to
                                       // scalars (complex structs)
      if (tpm->getName() == paramName) {
        overriden = true;
        if (ModuleInstance* pinst = instance->getParent()) {
          ModuleDefinition* pmod =
              valuedcomponenti_cast<ModuleDefinition*>(pinst->getDefinition());
          m_helper.checkForLoops(true);
          expr* rhs = (expr*)m_helper.compileExpression(
              pmod, tpm->getFileContent(), tpm->getNodeId(), m_compileDesign,
              isMultidimensional ? Reduce::No : Reduce::Yes, nullptr, pinst);
          m_helper.checkForLoops(false);
          if (en_replay && m_helper.errorOnNegativeConstant(
                               pmod, rhs, m_compileDesign, pinst)) {
            bool replay = false;
            // GDB: p replay=true
            if (replay) {
              m_helper.compileExpression(
                  pmod, tpm->getFileContent(), tpm->getNodeId(),
                  m_compileDesign,
                  isMultidimensional ? Reduce::No : Reduce::Yes, nullptr,
                  pinst);
            }
          }

          // If it is a complex expression (! constant)...
          if ((!rhs) || (rhs && (rhs->UhdmType() != uhdmconstant))) {
            // But if this value can be reduced to a constant then take the
            // constant
            m_helper.checkForLoops(true);
            expr* crhs = (expr*)m_helper.compileExpression(
                mod, assign->getFileContent(), assign->getAssignId(),
                m_compileDesign, Reduce::Yes, nullptr, instance);
            m_helper.checkForLoops(false);
            if (crhs && crhs->UhdmType() == uhdmconstant) {
              if (en_replay && m_helper.errorOnNegativeConstant(
                                   mod, crhs, m_compileDesign, instance)) {
                bool replay = false;
                // GDB: p replay=true
                if (replay) {
                  m_helper.compileExpression(
                      mod, assign->getFileContent(), assign->getAssignId(),
                      m_compileDesign, Reduce::Yes, nullptr, instance);
                }
              }

              constant* ccrhs = (constant*)crhs;
              const std::string_view s = ccrhs->VpiValue();
              Value* v1 = m_exprBuilder.fromVpiValue(s, ccrhs->VpiSize());
              Value* v2 = m_exprBuilder.fromVpiValue("INT:0", 64);
              if (*v1 > *v2) {
                rhs = crhs;
              }
            }
          }
          inst_assign->Rhs(rhs);
          break;
        }
      }
    }
    if ((overriden == false) && (!isMultidimensional)) {
      Value* value = instance->getValue(paramName, m_exprBuilder);
      if (value && value->isValid()) {
        constant* c = s.MakeConstant();
        const any* orig_p = mod_assign->Lhs();
        if (orig_p->UhdmType() == uhdmparameter) {
          if (ref_typespec* rt = ((parameter*)orig_p)->Typespec()) {
            if (typespec* ag = rt->Actual_typespec()) {
              ref_typespec* crt = s.MakeRef_typespec();
              crt->VpiParent(c);
              crt->Actual_typespec(ag);
              c->Typespec(crt);
            }
          }
        } else {
          if (ref_typespec* rt = ((type_parameter*)orig_p)->Typespec()) {
            if (typespec* ag = rt->Actual_typespec()) {
              ref_typespec* crt = s.MakeRef_typespec();
              crt->VpiParent(c);
              crt->Actual_typespec(ag);
              c->Typespec(crt);
            }
          }
        }
        c->VpiValue(value->uhdmValue());
        c->VpiDecompile(value->decompiledValue());
        c->VpiSize(value->getSize());
        c->VpiConstType(value->vpiValType());
        c->VpiParent(inst_assign);
        if (const typespec* ts = value->getTypespec()) {
          if (c->Typespec() == nullptr) {
            ref_typespec* tsRef = s.MakeRef_typespec();
            tsRef->VpiParent(c);
            c->Typespec(tsRef);
          }
          c->Typespec()->Actual_typespec((typespec*)ts);
        }
        assign->getFileContent()->populateCoreMembers(assign->getAssignId(),
                                                      assign->getAssignId(), c);
        inst_assign->Rhs(c);
        const UHDM::typespec* tps = nullptr;
        if (const UHDM::ref_typespec* rt = c->Typespec()) {
          tps = rt->Actual_typespec();
        }
        m_helper.adjustSize(tps, instance->getDefinition(), m_compileDesign,
                            instance, c);
        if (en_replay && m_helper.errorOnNegativeConstant(
                             mod, c, m_compileDesign, instance)) {
          bool replay = false;
          // GDB: p replay=true
          if (replay) {
            instance->getValue(paramName, m_exprBuilder);
          }
        }

        overriden = true;
      }
    }
    if (overriden == false) {
      expr* exp = instance->getComplexValue(paramName);
      if (exp) {
        if (!isMultidimensional) {
          bool invalidValue = false;
          m_helper.checkForLoops(true);
          if (expr* tmp = m_helper.reduceExpr(
                  exp, invalidValue, mod, m_compileDesign, instance,
                  fileSystem->toPathId(
                      exp->VpiFile(),
                      m_compileDesign->getCompiler()->getSymbolTable()),
                  exp->VpiLineNo(), nullptr, true)) {
            if (!invalidValue) exp = tmp;
          }
          m_helper.checkForLoops(false);
        }
        m_helper.setParentNoOverride(exp, inst_assign);
        inst_assign->Rhs(exp);

        if (en_replay && m_helper.errorOnNegativeConstant(
                             mod, exp, m_compileDesign, instance)) {
          bool replay = false;
          // GDB: p replay=true
          if (replay) {
            expr* exp = instance->getComplexValue(paramName);
            if (exp) {
              if (!isMultidimensional) {
                bool invalidValue = false;
                m_helper.checkForLoops(true);
                expr* tmp = m_helper.reduceExpr(
                    exp, invalidValue, mod, m_compileDesign, instance,
                    fileSystem->toPathId(
                        exp->VpiFile(),
                        m_compileDesign->getCompiler()->getSymbolTable()),
                    exp->VpiLineNo(), nullptr, true);
                m_helper.checkForLoops(false);
                if (tmp && (invalidValue == false)) exp = tmp;
              }
            }
          }
        }
        overriden = true;
      } else if (instance->isOverridenParam(paramName)) {
        // simple value
        Value* value = instance->getValue(paramName, m_exprBuilder);
        if (value && value->isValid()) {
          constant* c = s.MakeConstant();
          const any* orig_p = mod_assign->Lhs();
          if (orig_p->UhdmType() == uhdmparameter) {
            if (ref_typespec* rt = ((parameter*)orig_p)->Typespec()) {
              if (typespec* ag = rt->Actual_typespec()) {
                ref_typespec* crt = s.MakeRef_typespec();
                crt->VpiParent(c);
                crt->Actual_typespec(ag);
                c->Typespec(crt);
              }
            }
          } else {
            if (ref_typespec* rt = ((type_parameter*)orig_p)->Typespec()) {
              if (typespec* ag = rt->Actual_typespec()) {
                ref_typespec* crt = s.MakeRef_typespec();
                crt->VpiParent(c);
                crt->Actual_typespec(ag);
                c->Typespec(crt);
              }
            }
          }
          c->VpiValue(value->uhdmValue());
          c->VpiDecompile(value->decompiledValue());
          c->VpiSize(value->getSize());
          c->VpiConstType(value->vpiValType());
          assign->getFileContent()->populateCoreMembers(
              assign->getAssignId(), assign->getAssignId(), c);
          inst_assign->Rhs(c);
          overriden = true;
        }
      }
    }
    if (overriden == false) {
      // Default
      if (assign->getAssignId()) {
        m_helper.checkForLoops(true);
        expr* rhs = (expr*)m_helper.compileExpression(
            mod, assign->getFileContent(), assign->getAssignId(),
            m_compileDesign, isMultidimensional ? Reduce::No : Reduce::Yes,
            inst_assign, instance);
        m_helper.checkForLoops(false);
        inst_assign->Rhs(rhs);
      }
    }
    if (inst_assign->Rhs() &&
        m_helper.isOverloaded(inst_assign->Rhs(), m_compileDesign, instance)) {
      inst_assign->VpiOverriden(true);
    }
    if (const any* lhs = inst_assign->Lhs()) {
      const typespec* tps = nullptr;
      if (lhs->UhdmType() == uhdmparameter) {
        if (const ref_typespec* rt = ((parameter*)lhs)->Typespec()) {
          tps = rt->Actual_typespec();
        }
      } else {
        if (const ref_typespec* rt = ((type_parameter*)lhs)->Typespec()) {
          tps = rt->Actual_typespec();
        }
      }
      if (tps) {
        if (m_helper.isOverloaded(tps, m_compileDesign, instance)) {
          inst_assign->VpiOverriden(true);
        }
        const any* rhs = inst_assign->Rhs();
        if (rhs && rhs->UhdmType() == uhdmconstant) {
          constant* c = (constant*)rhs;
          m_helper.adjustSize(tps, instance->getDefinition(), m_compileDesign,
                              instance, c);
        }
      }
    }
    if (inst_assign) assigns->push_back(inst_assign);
  }
  return true;
}

bool NetlistElaboration::elaborate_(ModuleInstance* instance, bool recurse) {
  if (instance->isElaborated()) return true;
  FileSystem* const fileSystem = FileSystem::getInstance();
  Serializer& s = m_compileDesign->getSerializer();
  instance->setElaborated();
  Netlist* netlist = instance->getNetlist();
  bool elabPortsNets = false;
  VObjectType insttype = instance->getType();
  if ((insttype != VObjectType::paInterface_instantiation) &&
      (insttype != VObjectType::paConditional_generate_construct) &&
      (insttype != VObjectType::paLoop_generate_construct) &&
      (insttype != VObjectType::paGenerate_item) &&
      (insttype != VObjectType::paGenerate_region) &&
      (insttype != VObjectType::paGenerate_module_conditional_statement) &&
      (insttype != VObjectType::paGenerate_interface_conditional_statement) &&
      (insttype != VObjectType::paGenerate_module_loop_statement) &&
      (insttype != VObjectType::paGenerate_interface_loop_statement) &&
      (insttype != VObjectType::paGenerate_module_named_block) &&
      (insttype != VObjectType::paGenerate_interface_named_block) &&
      (insttype != VObjectType::paGenerate_module_block) &&
      (insttype != VObjectType::paGenerate_interface_block) &&
      (insttype != VObjectType::paGenerate_module_item) &&
      (insttype != VObjectType::paGenerate_interface_item) &&
      (insttype != VObjectType::paGenerate_begin_end_block)) {
    elabPortsNets = true;
  }

  if (netlist == nullptr) {
    netlist = new Netlist(instance);
    instance->setNetlist(netlist);
  }

  elab_parameters_(instance, true);
  if (elabPortsNets) {
    elab_ports_nets_(instance, true);
  }
  elab_parameters_(instance, false);

  DesignComponent* childDef = instance->getDefinition();
  if (ModuleDefinition* mm =
          valuedcomponenti_cast<ModuleDefinition*>(childDef)) {
    VObjectType insttype = instance->getType();
    if (insttype == VObjectType::paInterface_instantiation) {
      elab_interface_(
          instance->getParent(), instance, instance->getInstanceName(),
          instance->getModuleName(), mm,
          fileSystem->copy(instance->getFileId(),
                           m_compileDesign->getCompiler()->getSymbolTable()),
          instance->getLineNb(), nullptr, "");
    }
  }

  elab_generates_(instance);

  if (elabPortsNets) {
    elab_ports_nets_(instance, false);
  }

  high_conn_(instance);

  DesignComponent* component = instance->getDefinition();
  if (component) {
    if (UHDM::VectorOfcont_assign* cassigns = component->getContAssigns()) {
      std::vector<cont_assign*>* assigns = netlist->cont_assigns();
      if (assigns == nullptr) {
        netlist->cont_assigns(s.MakeCont_assignVec());
        assigns = netlist->cont_assigns();
      }
      for (cont_assign* assign : *cassigns) {
        assigns->push_back(assign);
      }
    }

    UHDM::VectorOfprocess_stmt* processes = netlist->process_stmts();
    if (processes == nullptr) {
      netlist->process_stmts(component->getProcesses());
    } else {
      if (component->getProcesses())
        for (auto proc : *component->getProcesses()) {
          netlist->process_stmts()->push_back(proc);
        }
    }
  }

  if (recurse) {
    for (uint32_t i = 0; i < instance->getNbChildren(); i++) {
      elaborate_(instance->getChildren(i), recurse);
    }
  }
  return true;
}

ModuleInstance* NetlistElaboration::getInterfaceInstance_(
    ModuleInstance* instance, std::string_view portName) {
  ModuleInstance* parent = instance->getParent();
  const FileContent* fC = instance->getFileContent();
  NodeId Udp_instantiation = instance->getNodeId();
  VObjectType inst_type = fC->Type(Udp_instantiation);

  if ((inst_type == VObjectType::paUdp_instantiation) ||
      (inst_type == VObjectType::paModule_instantiation) ||
      (inst_type == VObjectType::paProgram_instantiation) ||
      (inst_type == VObjectType::paInterface_instantiation) ||
      (inst_type == VObjectType::paCmos_switch_instance) ||
      (inst_type == VObjectType::paEnable_gate_instance) ||
      (inst_type == VObjectType::paMos_switch_instance) ||
      (inst_type == VObjectType::paN_input_gate_instance) ||
      (inst_type == VObjectType::paN_output_gate_instance) ||
      (inst_type == VObjectType::paPass_enable_switch_instance) ||
      (inst_type == VObjectType::paPass_switch_instance) ||
      (inst_type == VObjectType::paPull_gate_instance)) {
    NodeId modId = fC->Child(Udp_instantiation);
    NodeId Udp_instance = fC->Sibling(modId);
    if (fC->Type(Udp_instance) == VObjectType::paParameter_value_assignment) {
      Udp_instance = fC->Sibling(Udp_instance);
    } else if (fC->Type(Udp_instance) == VObjectType::paDelay2 ||
               fC->Type(Udp_instance) == VObjectType::paDelay3) {
      Udp_instance = fC->Sibling(Udp_instance);
      if (Udp_instance == InvalidNodeId) {
        Udp_instance = fC->Child(Udp_instance);
      }
    }
    NodeId Net_lvalue;
    if (const NodeId Name_of_instance = fC->Child(Udp_instance);
        fC->Type(Name_of_instance) == VObjectType::paName_of_instance) {
      Net_lvalue = fC->Sibling(Name_of_instance);
    } else {
      Net_lvalue = Name_of_instance;
    }
    if (fC->Type(Net_lvalue) == VObjectType::paNet_lvalue) {
      uint32_t index = 0;
      while (Net_lvalue) {
        std::string sigName;
        NodeId sigId;
        if (fC->Type(Net_lvalue) == VObjectType::paNet_lvalue) {
          NodeId Hierarchical_identifier = fC->Child(Net_lvalue);
          if (fC->Type(fC->Child(Hierarchical_identifier)) ==
              VObjectType::paHierarchical_identifier) {
            Hierarchical_identifier =
                fC->Child(fC->Child(Hierarchical_identifier));
          } else if (fC->Type(Hierarchical_identifier) !=
                     VObjectType::paPs_or_hierarchical_identifier) {
            Hierarchical_identifier = Net_lvalue;
          }
          sigId = Hierarchical_identifier;
          if (fC->Type(fC->Child(sigId)) == VObjectType::slStringConst) {
            sigId = fC->Child(sigId);
          }
          sigName = fC->SymName(sigId);
        } else if (fC->Type(Net_lvalue) == VObjectType::paExpression) {
          NodeId Primary = fC->Child(Net_lvalue);
          NodeId Primary_literal = fC->Child(Primary);
          sigId = fC->Child(Primary_literal);
          sigName = fC->SymName(sigId);
        }
        Net_lvalue = fC->Sibling(Net_lvalue);
        index++;
      }
    } else if (fC->Type(Net_lvalue) ==
               VObjectType::paList_of_port_connections) {
      NodeId Named_port_connection = fC->Child(Net_lvalue);
      uint32_t index = 0;
      bool orderedConnection = false;
      if (fC->Type(Named_port_connection) ==
          VObjectType::paOrdered_port_connection) {
        orderedConnection = true;
      }

      NodeId MemNamed_port_connection = Named_port_connection;
      while (Named_port_connection) {
        NodeId formalId = fC->Child(Named_port_connection);
        if (fC->Type(formalId) == VObjectType::paDOTSTAR) {
          // .* connection
          break;
        }
        Named_port_connection = fC->Sibling(Named_port_connection);
      }

      Named_port_connection = MemNamed_port_connection;
      while (Named_port_connection) {
        NodeId formalId = fC->Child(Named_port_connection);
        if (!formalId) break;
        if (fC->Type(formalId) == VObjectType::paDOTSTAR) {
          // .* connection
          Named_port_connection = fC->Sibling(Named_port_connection);
          continue;
        }

        std::string_view formalName = fC->SymName(formalId);
        NodeId Expression = fC->Sibling(formalId);
        if (orderedConnection) {
          Expression = formalId;
        } else {
          NodeId tmp = Expression;
          if (fC->Type(tmp) == VObjectType::paOPEN_PARENS) {
            tmp = fC->Sibling(tmp);
            if (fC->Type(tmp) ==
                VObjectType::paCLOSE_PARENS) {  // .p()  explicit disconnect
              Named_port_connection = fC->Sibling(Named_port_connection);
              index++;
              continue;
            } else if (fC->Type(tmp) ==
                       VObjectType::paExpression) {  // .p(s) connection by name
              formalId = tmp;
              Expression = tmp;
            }
          }  // else .p implicit connection
        }
        NodeId sigId = formalId;
        if (fC->Type(Expression) == VObjectType::paAttribute_instance) {
          while (fC->Type(Expression) == VObjectType::paAttribute_instance)
            Expression = fC->Sibling(Expression);
        }
        if (Expression) {
          NodeId Primary = fC->Child(Expression);
          NodeId Primary_literal = fC->Child(Primary);
          sigId = fC->Child(Primary_literal);
        }
        std::string sigName;
        if (sigId && fC->Name(sigId)) sigName = fC->SymName(sigId);
        std::string baseName = sigName;
        std::string selectName;
        if (NodeId subId = fC->Sibling(sigId)) {
          if (fC->Name(subId)) {
            selectName = fC->SymName(subId);
            sigName += std::string(".") + selectName;
          }
        }
        if (formalName == portName) {
          for (auto inst : parent->getAllSubInstances()) {
            if (inst->getInstanceName() == sigName) {
              return inst;
            }
          }
        }
        Named_port_connection = fC->Sibling(Named_port_connection);
        index++;
      }
    }
  }
  return nullptr;
}

bool NetlistElaboration::high_conn_(ModuleInstance* instance) {
  FileSystem* const fileSystem = FileSystem::getInstance();
  ModuleInstance* parent = instance->getParent();
  DesignComponent* parent_comp = nullptr;
  if (parent) parent_comp = parent->getDefinition();
  const FileContent* fC = instance->getFileContent();
  NodeId Udp_instantiation = instance->getNodeId();
  Serializer& s = m_compileDesign->getSerializer();
  Netlist* netlist = instance->getNetlist();
  VObjectType inst_type = fC->Type(Udp_instantiation);
  std::vector<UHDM::port*>* ports = netlist->ports();
  DesignComponent* comp = instance->getDefinition();
  std::vector<Signal*>* signals = nullptr;
  std::string instName = instance->getInstanceName();
  bool instanceArray = false;
  int32_t instanceArrayIndex = 0;
  {
    std::string indexS;
    bool inValue = false;
    if (!instName.empty()) {
      for (uint64_t i = instName.size() - 1; i > 1; i--) {
        char c = instName[i];
        if (c == '[') {
          break;
        }
        if (inValue) {
          indexS += c;
        }
        if (c == ']') {
          instanceArray = true;
          inValue = true;
        }
      }
    }
    if (!indexS.empty()) {
      std::reverse(indexS.begin(), indexS.end());
      instanceArrayIndex = std::atoll(indexS.c_str());
    }
  }
  if (comp) {
    signals = &comp->getPorts();
  }
  std::map<std::string_view, Signal*> allSignals;
  std::map<std::string_view, Signal*> allSignalsConst;
  if (signals) {
    for (Signal* s : *signals) {
      allSignals.emplace(s->getName(), s);
      allSignalsConst.emplace(s->getName(), s);
    }
  }
  if ((inst_type == VObjectType::paUdp_instantiation) ||
      (inst_type == VObjectType::paModule_instantiation) ||
      (inst_type == VObjectType::paProgram_instantiation) ||
      (inst_type == VObjectType::paInterface_instantiation) ||
      (inst_type == VObjectType::paCmos_switch_instance) ||
      (inst_type == VObjectType::paEnable_gate_instance) ||
      (inst_type == VObjectType::paMos_switch_instance) ||
      (inst_type == VObjectType::paN_input_gate_instance) ||
      (inst_type == VObjectType::paN_output_gate_instance) ||
      (inst_type == VObjectType::paPass_enable_switch_instance) ||
      (inst_type == VObjectType::paPass_switch_instance) ||
      (inst_type == VObjectType::paPull_gate_instance)) {
    /*
    n<DUT> u<178> t<StringConst> p<191> s<190> l<20>
    n<dut> u<179> t<StringConst> p<180> l<20>
    n<> u<180> t<Name_of_instance> p<190> c<179> s<185> l<20>
    n<i> u<181> t<StringConst> p<182> l<20>
    n<> u<182> t<Ps_or_hierarchical_identifier> p<185> c<181> s<184> l<20>
    n<> u<183> t<Constant_bit_select> p<184> l<20>
    n<> u<184> t<Constant_select> p<185> c<183> l<20>
    n<> u<185> t<Net_lvalue> p<190> c<182> s<189> l<20>
    n<o> u<186> t<StringConst> p<187> l<20>
    n<> u<187> t<Primary_literal> p<188> c<186> l<20>
    n<> u<188> t<Primary> p<189> c<187> l<20>
    n<> u<189> t<Expression> p<190> c<188> l<20>
    n<> u<190> t<Udp_instance> p<191> c<180> l<20>
    n<> u<191> t<Udp_instantiation> p<192> c<178> l<20>
    */
    NodeId modId = fC->Child(Udp_instantiation);
    NodeId Udp_instance = fC->Sibling(modId);
    if ((inst_type == VObjectType::paCmos_switch_instance) ||
        (inst_type == VObjectType::paEnable_gate_instance) ||
        (inst_type == VObjectType::paMos_switch_instance) ||
        (inst_type == VObjectType::paN_input_gate_instance) ||
        (inst_type == VObjectType::paN_output_gate_instance) ||
        (inst_type == VObjectType::paPass_enable_switch_instance) ||
        (inst_type == VObjectType::paPass_switch_instance) ||
        (inst_type == VObjectType::paPull_gate_instance)) {
      modId = fC->Child(fC->Parent(Udp_instantiation));
      Udp_instance = Udp_instantiation;
      // In the case of single instance, point to the delay or parameter
      NodeId tmp = fC->Sibling(modId);
      if ((fC->Type(tmp) == VObjectType::paParameter_value_assignment) ||
          (fC->Type(tmp) == VObjectType::paDelay2) ||
          (fC->Type(tmp) == VObjectType::paDelay3)) {
        Udp_instance = tmp;
      }
    }
    if (fC->Type(Udp_instance) == VObjectType::paParameter_value_assignment) {
      Udp_instance = fC->Sibling(Udp_instance);
    } else if (fC->Type(Udp_instance) == VObjectType::paDelay2 ||
               fC->Type(Udp_instance) == VObjectType::paDelay3) {
      m_helper.checkForLoops(true);
      expr* delay_expr = (expr*)m_helper.compileExpression(
          parent_comp, fC, Udp_instance, m_compileDesign, Reduce::Yes, nullptr,
          parent);
      m_helper.checkForLoops(false);
      VectorOfexpr* delays = s.MakeExprVec();
      netlist->delays(delays);
      delays->push_back(delay_expr);
      Udp_instance = fC->Sibling(Udp_instance);
    }
    NodeId Net_lvalue;
    if (const NodeId Name_of_instance = fC->Child(Udp_instance);
        fC->Type(Name_of_instance) == VObjectType::paName_of_instance) {
      Net_lvalue = fC->Sibling(Name_of_instance);
      NodeId Name = fC->Child(Name_of_instance);
      NodeId Unpacked_dimension = fC->Sibling(Name);
      if (Unpacked_dimension) {
        int32_t size;
        m_helper.checkForLoops(true);
        VectorOfrange* ranges = m_helper.compileRanges(
            comp, fC, Unpacked_dimension, m_compileDesign, Reduce::Yes, nullptr,
            parent, size, false);
        m_helper.checkForLoops(false);
        netlist->ranges(ranges);
      }
    } else {
      Net_lvalue = Name_of_instance;
    }
    if (fC->Type(Net_lvalue) == VObjectType::paNet_lvalue) {
      uint32_t index = 0;
      while (Net_lvalue) {
        std::string sigName;
        NodeId sigId;
        bool bit_or_part_select = false;
        if (fC->Type(Net_lvalue) == VObjectType::paNet_lvalue) {
          NodeId Hierarchical_identifier = fC->Child(Net_lvalue);
          if (fC->Type(fC->Child(Hierarchical_identifier)) ==
              VObjectType::paHierarchical_identifier) {
            Hierarchical_identifier =
                fC->Child(fC->Child(Hierarchical_identifier));
          } else if (fC->Type(Hierarchical_identifier) !=
                     VObjectType::paPs_or_hierarchical_identifier) {
            Hierarchical_identifier = Net_lvalue;
          }
          if (m_helper.isSelected(fC, Hierarchical_identifier))
            bit_or_part_select = true;
          sigId = Hierarchical_identifier;
          if (fC->Type(fC->Child(sigId)) == VObjectType::slStringConst) {
            sigId = fC->Child(sigId);
          }
          sigName = fC->SymName(sigId);
        } else if (fC->Type(Net_lvalue) == VObjectType::paExpression) {
          NodeId Primary = fC->Child(Net_lvalue);
          NodeId Primary_literal = fC->Child(Primary);
          if (fC->Type(Primary_literal) == VObjectType::paComplex_func_call)
            bit_or_part_select = true;
          sigId = fC->Child(Primary_literal);
          sigName = fC->SymName(sigId);
        }
        if (ports) {
          if (index < ports->size()) {
            port* p = (*ports)[index];

            if ((!bit_or_part_select) &&
                (fC->Type(sigId) == VObjectType::slStringConst)) {
              bool bitBlast = false;
              any* net = nullptr;
              if (parent) {
                net = bind_net_(fC, sigId, parent,
                                instance->getInstanceBinding(), sigName);
              }
              if (instanceArray) {
                if (parent) {
                  if (net) {
                    UHDM_OBJECT_TYPE ntype = net->UhdmType();
                    if (ntype == uhdmlogic_net) {
                      logic_net* lnet = (logic_net*)net;
                      if (const ref_typespec* rt = lnet->Typespec()) {
                        if (const logic_typespec* tps =
                                rt->Actual_typespec<logic_typespec>()) {
                          if (tps->Ranges()) bitBlast = true;
                        }
                      }
                    } else if (ntype == uhdmarray_net) {
                      array_net* lnet = (array_net*)net;
                      if (const ref_typespec* rt = lnet->Typespec()) {
                        if (const array_typespec* tps =
                                rt->Actual_typespec<array_typespec>()) {
                          if (tps->Ranges()) bitBlast = true;
                        }
                      }
                    }
                  }
                }
              }
              if (bitBlast) {
                bit_select* sel = s.MakeBit_select();
                sel->VpiName(sigName);
                constant* c = s.MakeConstant();
                c->VpiValue("UINT:" + std::to_string(instanceArrayIndex));
                c->VpiDecompile(std::to_string(instanceArrayIndex));
                c->VpiSize(64);
                fC->populateCoreMembers(sigId, sigId, c);
                sel->VpiIndex(c);
                sel->VpiParent(p);
                p->High_conn(sel);
                fC->populateCoreMembers(sigId, sigId, sel);
                sel->Actual_group(net);
              } else {
                ref_obj* ref = s.MakeRef_obj();
                fC->populateCoreMembers(sigId, sigId, ref);
                p->High_conn(ref);
                ref->VpiParent(p);
                ref->VpiName(sigName);
                if (parent) {
                  ref->VpiFullName(parent->getFullPathName() + "." + sigName);
                  ref->Actual_group(net);
                }
              }
            } else {
              any* exp = nullptr;
              if (fC->Type(Net_lvalue) == VObjectType::paNet_lvalue) {
                NodeId Hierarchical_identifier = fC->Child(Net_lvalue);
                if (fC->Type(fC->Child(Hierarchical_identifier)) ==
                    VObjectType::paHierarchical_identifier) {
                  Hierarchical_identifier =
                      fC->Child(fC->Child(Hierarchical_identifier));
                } else if (fC->Type(Hierarchical_identifier) !=
                           VObjectType::paPs_or_hierarchical_identifier) {
                  Hierarchical_identifier = Net_lvalue;
                }
                m_helper.checkForLoops(true);
                exp = m_helper.compileExpression(
                    parent_comp, fC, Hierarchical_identifier, m_compileDesign,
                    Reduce::Yes, p, parent);
                m_helper.checkForLoops(false);
              } else {
                m_helper.checkForLoops(true);
                exp = m_helper.compileExpression(parent_comp, fC, Net_lvalue,
                                                 m_compileDesign, Reduce::Yes,
                                                 p, parent);
                m_helper.checkForLoops(false);
              }
              if (exp != nullptr) {
                p->High_conn(exp);
                exp->VpiParent(p);
              }
            }
          }
        }
        if ((inst_type == VObjectType::paCmos_switch_instance) ||
            (inst_type == VObjectType::paEnable_gate_instance) ||
            (inst_type == VObjectType::paMos_switch_instance) ||
            (inst_type == VObjectType::paN_input_gate_instance) ||
            (inst_type == VObjectType::paN_output_gate_instance) ||
            (inst_type == VObjectType::paPass_enable_switch_instance) ||
            (inst_type == VObjectType::paPass_switch_instance) ||
            (inst_type == VObjectType::paPull_gate_instance) ||
            (inst_type == VObjectType::paUdp_instantiation)) {
          port* p = s.MakePort();
          if (ports == nullptr) {
            ports = s.MakePortVec();
            netlist->ports(ports);
          }
          fC->populateCoreMembers(Net_lvalue, Net_lvalue, p);
          if ((fC->Type(sigId) == VObjectType::slStringConst) &&
              (!bit_or_part_select)) {
            ref_obj* ref = s.MakeRef_obj();
            fC->populateCoreMembers(sigId, sigId, ref);
            p->High_conn(ref);
            ref->VpiName(sigName);
            ref->VpiParent(p);
            if (parent) {
              ref->VpiFullName(parent->getFullPathName() + "." + sigName);
              if (any* net =
                      bind_net_(fC, sigId, parent,
                                instance->getInstanceBinding(), sigName)) {
                ref->Actual_group(net);
              }
            }
          } else {
            NodeId Hierarchical_identifier = fC->Child(Net_lvalue);
            if (fC->Type(fC->Child(Hierarchical_identifier)) ==
                VObjectType::paHierarchical_identifier) {
              Hierarchical_identifier =
                  fC->Child(fC->Child(Hierarchical_identifier));
            } else if (fC->Type(Hierarchical_identifier) !=
                       VObjectType::paPs_or_hierarchical_identifier) {
              Hierarchical_identifier = Net_lvalue;
            }
            m_helper.checkForLoops(true);
            any* exp = m_helper.compileExpression(
                parent_comp, fC, Hierarchical_identifier, m_compileDesign,
                Reduce::Yes, nullptr, parent);
            m_helper.checkForLoops(false);
            p->High_conn(exp);
            exp->VpiParent(p);
            if (exp->UhdmType() == uhdmref_obj) {
              ref_obj* ref = (ref_obj*)exp;
              const std::string_view n = ref->VpiName();
              if (any* net = bind_net_(fC, Hierarchical_identifier, parent,
                                       instance->getInstanceBinding(), n)) {
                ref->Actual_group(net);
              }
            }
          }
          ports->push_back(p);
        }
        Net_lvalue = fC->Sibling(Net_lvalue);
        index++;
      }
    } else if (fC->Type(Net_lvalue) ==
               VObjectType::paList_of_port_connections) {
      /*
      n<TESTBENCH> u<195> t<StringConst> p<212> s<211> l<21>
      n<tb> u<196> t<StringConst> p<197> l<21>
      n<> u<197> t<Name_of_instance> p<211> c<196> s<210> l<21>
      n<observe> u<198> t<StringConst> p<203> s<202> l<21>
      n<o> u<199> t<StringConst> p<200> l<21>
      n<> u<200> t<Primary_literal> p<201> c<199> l<21>
      n<> u<201> t<Primary> p<202> c<200> l<21>
      n<> u<202> t<Expression> p<203> c<201> l<21>
      n<> u<203> t<Named_port_connection> p<210> c<198> s<209> l<21>
      n<drive> u<204> t<StringConst> p<209> s<208> l<21>
      n<i> u<205> t<StringConst> p<206> l<21>
      n<> u<206> t<Primary_literal> p<207> c<205> l<21>
      n<> u<207> t<Primary> p<208> c<206> l<21>
      n<> u<208> t<Expression> p<209> c<207> l<21>
      n<> u<209> t<Named_port_connection> p<210> c<204> l<21>
      n<> u<210> t<List_of_port_connections> p<211> c<203> l<21>
      n<> u<211> t<Hierarchical_instance> p<212> c<197> l<21>
      n<> u<212> t<Module_instantiation> p<213> c<195> l<21>
      */
      NodeId Named_port_connection = fC->Child(Net_lvalue);
      uint32_t index = 0;
      bool orderedConnection = false;
      if (fC->Type(Named_port_connection) ==
          VObjectType::paOrdered_port_connection) {
        orderedConnection = true;
      }

      bool wildcard = false;
      NodeId MemNamed_port_connection = Named_port_connection;
      uint32_t wildcardLineNumber = 0;
      uint16_t wildcardColumnNumber = 0;
      while (Named_port_connection) {
        NodeId formalId = fC->Child(Named_port_connection);
        if (fC->Type(formalId) == VObjectType::paDOTSTAR) {
          // .* connection
          wildcard = true;
          wildcardLineNumber = fC->Line(formalId);
          wildcardColumnNumber = fC->Column(formalId);
          break;
        }
        Named_port_connection = fC->Sibling(Named_port_connection);
      }

      Named_port_connection = MemNamed_port_connection;
      while (Named_port_connection) {
        NodeId formalId = fC->Child(Named_port_connection);
        if (!formalId) {
          Named_port_connection = fC->Sibling(Named_port_connection);
          index++;
          continue;
        }
        UHDM::VectorOfattribute* attributes = nullptr;
        if (fC->Type(formalId) == VObjectType::paAttribute_instance) {
          attributes = m_helper.compileAttributes(parent_comp, fC, formalId,
                                                  m_compileDesign, nullptr);
          while (fC->Type(formalId) == VObjectType::paAttribute_instance) {
            formalId = fC->Sibling(formalId);
          }
        }
        if (fC->Type(formalId) == VObjectType::paDOTSTAR) {
          // .* connection
          Named_port_connection = fC->Sibling(Named_port_connection);
          continue;
        }

        NodeId sigId = formalId;
        std::string_view formalName = fC->SymName(formalId);
        NodeId Expression = fC->Sibling(formalId);
        if (orderedConnection) {
          Expression = formalId;
          NodeId Primary = fC->Child(Expression);
          NodeId Primary_literal = fC->Child(Primary);
          NodeId formalNameId = fC->Child(Primary_literal);
          formalName = fC->SymName(formalNameId);
        } else {
          NodeId tmp = Expression;
          if (fC->Type(tmp) == VObjectType::paOPEN_PARENS) {
            tmp = fC->Sibling(tmp);
            if (fC->Type(tmp) ==
                VObjectType::paCLOSE_PARENS) {  // .p()  explicit disconnect
              Named_port_connection = fC->Sibling(Named_port_connection);
              port* p = nullptr;
              if (ports) {
                if (index < ports->size()) {
                  if (orderedConnection) {
                    formalName = ((*signals)[index])->getName();
                    p = (*ports)[index];
                  } else {
                    for (port* pItr : *ports) {
                      if (pItr->VpiName() == formalName) {
                        p = pItr;
                        break;
                      }
                    }
                    if (p == nullptr) p = (*ports)[index];
                  }
                } else {
                  p = s.MakePort();
                  ports->push_back(p);
                  p->VpiName(formalName);
                  fC->populateCoreMembers(formalId, formalId, p);
                  if (!allSignalsConst.empty()) {
                    auto found = allSignalsConst.find(p->VpiName());
                    if (found == allSignalsConst.end()) {
                      SymbolTable* symbols =
                          m_compileDesign->getCompiler()->getSymbolTable();
                      ErrorContainer* errors =
                          m_compileDesign->getCompiler()->getErrorContainer();
                      Location loc(
                          fileSystem->toPathId(
                              p->VpiFile(),
                              m_compileDesign->getCompiler()->getSymbolTable()),
                          p->VpiLineNo(), p->VpiColumnNo(),
                          symbols->registerSymbol(p->VpiName()));
                      Error err(ErrorDefinition::ELAB_UNKNOWN_PORT, loc);
                      errors->addError(err);
                    }
                  }
                }
              } else {
                ports = s.MakePortVec();
                netlist->ports(ports);
                p = s.MakePort();
                ports->push_back(p);
                p->VpiName(formalName);
                fC->populateCoreMembers(formalId, formalId, p);
              }
              operation* op = s.MakeOperation();
              op->VpiOpType(vpiNullOp);
              fC->populateCoreMembers(tmp, tmp, op);
              op->VpiParent(p);
              p->High_conn(op);
              index++;
              continue;
            } else if (fC->Type(tmp) ==
                       VObjectType::paExpression) {  // .p(s) connection by name
              sigId = tmp;
              Expression = tmp;
              if (!allSignalsConst.empty()) {
                auto found = allSignalsConst.find(formalName);
                if (found == allSignalsConst.end()) {
                  SymbolTable* symbols =
                      m_compileDesign->getCompiler()->getSymbolTable();
                  ErrorContainer* errors =
                      m_compileDesign->getCompiler()->getErrorContainer();
                  Location loc(fC->getFileId(formalId), fC->Line(formalId),
                               fC->Column(formalId),
                               symbols->registerSymbol(formalName));
                  Error err(ErrorDefinition::ELAB_UNKNOWN_PORT, loc);
                  errors->addError(err);
                }
              }
            }
          }  // else .p implicit connection
        }
        expr* hexpr = nullptr;
        if (fC->Type(Expression) == VObjectType::paAttribute_instance) {
          attributes = m_helper.compileAttributes(comp, fC, Expression,
                                                  m_compileDesign, nullptr);
          while (fC->Type(Expression) == VObjectType::paAttribute_instance)
            Expression = fC->Sibling(Expression);
        }
        if (Expression) {
          m_helper.checkForLoops(true);
          hexpr = (expr*)m_helper.compileExpression(
              parent_comp, fC, Expression, m_compileDesign, Reduce::Yes,
              nullptr, parent);
          m_helper.checkForLoops(false);
          NodeId Primary = fC->Child(Expression);
          NodeId Primary_literal = fC->Child(Primary);
          sigId = fC->Child(Primary_literal);
        }
        std::string sigName;
        bool modPort = true;
        if (hexpr && hexpr->UhdmType() == uhdmhier_path) {
          hier_path* hier = (hier_path*)hexpr;
          for (auto p : *hier->Path_elems()) {
            if (p->UhdmType() != uhdmref_obj) {
              modPort = false;
              break;
            }
          }
        }
        if (modPort) {
          if (fC->Type(sigId) == VObjectType::slStringConst)
            sigName = fC->SymName(sigId);
        }
        std::string baseName = sigName;
        std::string selectName;
        if (NodeId subId = fC->Sibling(sigId)) {
          if (fC->Name(subId)) {
            selectName = fC->SymName(subId);
            sigName += std::string(".") + selectName;
          }
        }
        port* p = nullptr;
        if (ports) {
          if (index < ports->size()) {
            if (orderedConnection) {
              formalName = ((*signals)[index])->getName();
              p = (*ports)[index];
            } else {
              for (port* pItr : *ports) {
                if (pItr->VpiName() == formalName) {
                  p = pItr;
                  break;
                }
              }
              if (p == nullptr) p = (*ports)[index];
            }
          } else {
            p = s.MakePort();
            ports->push_back(p);
          }
        } else {
          ports = s.MakePortVec();
          netlist->ports(ports);
          p = s.MakePort();
          ports->push_back(p);
        }
        any* net = nullptr;
        if (!sigName.empty()) {
          net = bind_net_(fC, sigId, parent, instance->getInstanceBinding(),
                          sigName);
        }

        if ((!sigName.empty()) && (hexpr == nullptr)) {
          ref_obj* ref = s.MakeRef_obj();
          fC->populateCoreMembers(sigId, sigId, ref);
          ref->VpiName(sigName);
          if (parent) {
            ref->VpiFullName(parent->getFullPathName() + "." + sigName);
            ref->VpiParent(p);
            p->High_conn(ref);
            ref->Actual_group(net);
          }
        } else if (hexpr != nullptr) {
          if (hexpr && hexpr->UhdmType() == uhdmoperation) {
            operation* op = (operation*)hexpr;
            int32_t opType = op->VpiOpType();
            const typespec* tps = nullptr;
            if (p && p->Typespec()) {
              tps = p->Typespec()->Actual_typespec();
            }
            if (opType == vpiAssignmentPatternOp) {
              if (m_helper.substituteAssignedValue(hexpr, m_compileDesign)) {
                hexpr = m_helper.expandPatternAssignment(
                    tps, (UHDM::expr*)hexpr, parent_comp, m_compileDesign,
                    netlist->getParent());
              }
            }
            hexpr = (UHDM::expr*)m_helper.defaultPatternAssignment(
                tps, (UHDM::expr*)hexpr, parent_comp, m_compileDesign,
                netlist->getParent());
            if (p) {
              if (const any* lowc = p->Low_conn()) {
                if (lowc->UhdmType() == uhdmref_obj) {
                  ref_obj* ref = (ref_obj*)lowc;
                  m_helper.reorderAssignmentPattern(
                      parent_comp, ref->Actual_group(), (UHDM::expr*)hexpr,
                      m_compileDesign, netlist->getParent(), 0);
                }
              }
            }
          }
          p->High_conn(hexpr);
          hexpr->VpiParent(p);
          if (hexpr->UhdmType() == uhdmref_obj) {
            ((ref_obj*)hexpr)->VpiParent(p);
            ((ref_obj*)hexpr)->Actual_group(net);
            if (parent) {
              ((ref_obj*)hexpr)
                  ->VpiFullName(StrCat(parent->getFullPathName(), ".",
                                       ((ref_obj*)hexpr)->VpiName()));
            }
          }
        }
        p->VpiName(formalName);
        if (attributes) {
          p->Attributes(attributes);
          for (auto a : *attributes) a->VpiParent(p);
        }
        if (p->VpiLineNo() == 0) {
          fC->populateCoreMembers(formalId, formalId, p);
        }
        bool lowconn_is_nettype = false;
        if (const any* lc = p->Low_conn()) {
          if (lc->UhdmType() == uhdmref_obj) {
            ref_obj* rf = (ref_obj*)lc;
            fC->populateCoreMembers(formalId, formalId, rf);
            const any* act = rf->Actual_group();
            if (act && (act->UhdmType() == uhdmlogic_net))
              lowconn_is_nettype = true;
          }
        }
        if (net && (net->UhdmType() == uhdmmodport) && (lowconn_is_nettype)) {
          Netlist* parentNetlist = parent->getNetlist();
          Netlist::ModPortMap::iterator itr;
          modport* mp = nullptr;
          if (orderedConnection) {
            itr = netlist->getModPortMap().find(formalName);
            if (itr != netlist->getModPortMap().end()) {
              mp = (*itr).second.second;
            }
          } else {
            itr = parentNetlist->getModPortMap().find(sigName);
            if (itr != parentNetlist->getModPortMap().end()) {
              ModPort* orig_modport = (*itr).second.first;
              ModuleDefinition* orig_interf = orig_modport->getParent();

              ModuleInstance* interfaceInstance =
                  new ModuleInstance(orig_interf, fC, sigId, instance, sigName,
                                     orig_interf->getName());
              Netlist* netlistInterf = new Netlist(interfaceInstance);
              interfaceInstance->setNetlist(netlistInterf);

              mp = elab_modport_(
                  instance, interfaceInstance, formalName,
                  orig_interf->getName(), orig_interf,
                  fileSystem->toPathId(
                      p->VpiFile(),
                      m_compileDesign->getCompiler()->getSymbolTable()),
                  p->VpiLineNo(), selectName, nullptr);
            }
          }
          if (mp) {
            ref_obj* ref = s.MakeRef_obj();
            ref->VpiFile(p->VpiFile());
            ref->VpiLineNo(p->VpiLineNo());
            ref->VpiColumnNo(p->VpiColumnNo());
            ref->VpiEndLineNo(p->VpiEndLineNo());
            ref->VpiEndColumnNo(p->VpiEndColumnNo());
            ref->VpiParent(p);
            ref->Actual_group(mp);
            p->Low_conn(ref);
          }
        } else if (net && (net->UhdmType() == uhdminterface_inst) &&
                   (lowconn_is_nettype)) {
          BaseClass* sm = nullptr;
          if (orderedConnection) {
            Netlist::InstanceMap::iterator itr =
                netlist->getInstanceMap().find(formalName);
            if (itr != netlist->getInstanceMap().end()) {
              sm = (*itr).second.second;
            }
          } else {
            Netlist* parentNetlist = parent->getNetlist();
            Netlist::InstanceMap::iterator itr =
                parentNetlist->getInstanceMap().find(sigName);
            if (itr != parentNetlist->getInstanceMap().end()) {
              ModuleInstance* orig_instance = (*itr).second.first;
              ModuleDefinition* orig_interf =
                  (ModuleDefinition*)orig_instance->getDefinition();
              sm = elab_interface_(
                  instance, orig_instance, formalName, orig_interf->getName(),
                  orig_interf,
                  fileSystem->copy(
                      instance->getFileId(),
                      m_compileDesign->getCompiler()->getSymbolTable()),
                  instance->getLineNb(), nullptr, "");
            }
          }
          if (sm) {
            ref_obj* ref = s.MakeRef_obj();
            ref->VpiParent(p);
            ref->Actual_group(sm);
            fC->populateCoreMembers(Named_port_connection,
                                    Named_port_connection, ref);
            p->Low_conn(ref);
          }
        }
        auto itr = allSignals.find(formalName);
        if (itr != allSignals.end()) {
          allSignals.erase(itr);
        }
        Named_port_connection = fC->Sibling(Named_port_connection);
        index++;
      }
      if (signals) {
        uint32_t formalSize = 0;
        if (ports) {
          formalSize = ports->size();
        }
        if (wildcard) {
          // Add missing ports
          VectorOfport* newPorts = s.MakePortVec();
          for (Signal* s1 : *signals) {
            const std::string_view sigName = s1->getName();
            bool found = false;
            port* pp = nullptr;
            for (port* p : *ports) {
              if (p->VpiName() == s1->getName()) {
                newPorts->push_back(p);
                found = true;
                pp = p;
                break;
              }
            }
            if (!found) {
              port* p = s.MakePort();
              p->VpiName(sigName);
              p->VpiFile(fileSystem->toPath(fC->getFileId()));
              p->VpiLineNo(wildcardLineNumber);
              p->VpiColumnNo(wildcardColumnNumber);
              p->VpiEndLineNo(wildcardLineNumber);
              p->VpiEndColumnNo(wildcardColumnNumber + 1);
              newPorts->push_back(p);
              pp = p;
            }
            if (pp->High_conn() == nullptr) {
              ref_obj* ref = s.MakeRef_obj();
              ref->VpiFile(fileSystem->toPath(fC->getFileId()));
              ref->VpiLineNo(wildcardLineNumber);
              ref->VpiColumnNo(wildcardColumnNumber);
              ref->VpiEndLineNo(wildcardLineNumber);
              ref->VpiEndColumnNo(wildcardColumnNumber + 1);
              ref->VpiName(sigName);
              ref->VpiParent(pp);
              if (parent) {
                ref->VpiFullName(
                    StrCat(parent->getFullPathName(), ".", sigName));
                pp->High_conn(ref);
                if (UHDM::any* net =
                        bind_net_(fC, InvalidNodeId, parent,
                                  instance->getInstanceBinding(), sigName)) {
                  ref->Actual_group(net);
                }
              }
            }
          }
          netlist->ports(newPorts);
        } else if (index < formalSize) {
          // Add missing ports
          VectorOfport* newPorts = s.MakePortVec();
          for (Signal* s1 : *signals) {
            const std::string_view sigName = s1->getName();

            auto itr = allSignals.find(sigName);
            if (itr != allSignals.end()) {
              auto pair = (*itr);
              port* p = nullptr;
              for (port* pt : *ports) {
                if (pt->VpiName() == sigName) {
                  p = pt;
                  newPorts->push_back(p);
                  break;
                }
              }

              if (p) {
                if (NodeId defaultId = pair.second->getDefaultValue()) {
                  m_helper.checkForLoops(true);
                  if (expr* exp = (expr*)m_helper.compileExpression(
                          comp, fC, defaultId, m_compileDesign, Reduce::Yes, p,
                          instance)) {
                    p->High_conn(exp);
                  }
                  m_helper.checkForLoops(false);
                }
              }
            } else {
              for (port* pt : *ports) {
                if (pt->VpiName() == sigName) {
                  newPorts->push_back(pt);
                  break;
                }
              }
            }
          }
          netlist->ports(newPorts);
        }
      }
    }
  }
  // Finally any unconnected ports with default value gets assigned the value
  if (ports) {
    for (auto p : *ports) {
      if (p->High_conn() != nullptr) continue;
      auto found = allSignals.find(p->VpiName());
      if (found == allSignals.end()) continue;
      if (NodeId defaultId = (*found).second->getDefaultValue()) {
        m_helper.checkForLoops(true);
        if (expr* exp = (expr*)m_helper.compileExpression(
                comp, fC, defaultId, m_compileDesign, Reduce::Yes, p,
                instance)) {
          p->High_conn(exp);
        }
        m_helper.checkForLoops(false);
      }
    }
  }
  return true;
}

interface_inst* NetlistElaboration::elab_interface_(
    ModuleInstance* instance, ModuleInstance* interf_instance,
    std::string_view instName, std::string_view defName, ModuleDefinition* mod,
    PathId fileId, uint32_t lineNb, interface_array* interf_array,
    std::string_view modPortName) {
  FileSystem* const fileSystem = FileSystem::getInstance();
  Netlist* netlist = instance->getNetlist();
  if (netlist == nullptr) {
    netlist = new Netlist(instance);
    instance->setNetlist(netlist);
  }
  Serializer& s = m_compileDesign->getSerializer();
  VectorOfinterface_inst* subInterfaces = netlist->interfaces();
  if (subInterfaces == nullptr) {
    subInterfaces = s.MakeInterface_instVec();
    netlist->interfaces(subInterfaces);
  }
  interface_inst* sm = s.MakeInterface_inst();
  sm->VpiName(instName);
  sm->VpiDefName(defName);
  // sm->VpiFullName(??);
  sm->VpiFile(fileSystem->toPath(fileId));
  sm->VpiLineNo(lineNb);
  subInterfaces->push_back(sm);
  if (interf_array) {
    sm->VpiParent(interf_array);
    interf_array->Instances()->push_back(sm);
    netlist->getInstanceMap().emplace(
        instName, std::make_pair(interf_instance, interf_array));
    netlist->getSymbolTable().emplace(instName, interf_array);
  } else {
    netlist->getInstanceMap().emplace(instName,
                                      std::make_pair(interf_instance, sm));
    netlist->getSymbolTable().emplace(instName, sm);
  }
  const std::string prefix = StrCat(instName, ".");
  elab_ports_nets_(instance, interf_instance, instance->getNetlist(),
                   interf_instance->getNetlist(), mod, prefix, true);
  elab_ports_nets_(instance, interf_instance, instance->getNetlist(),
                   interf_instance->getNetlist(), mod, prefix, false);
  // Modports
  ModuleDefinition::ModPortSignalMap& orig_modports =
      mod->getModPortSignalMap();
  VectorOfmodport* dest_modports = s.MakeModportVec();
  for (auto& orig_modport : orig_modports) {
    const std::string modportfullname =
        StrCat(instName, ".", orig_modport.first);
    if (!modPortName.empty() && (modportfullname != modPortName)) continue;
    modport* dest_modport = s.MakeModport();
    dest_modport->Interface_inst(sm);
    dest_modport->VpiParent(sm);
    const FileContent* orig_fC = orig_modport.second.getFileContent();
    const NodeId orig_nodeId = orig_modport.second.getNodeId();
    orig_fC->populateCoreMembers(orig_nodeId, orig_nodeId, dest_modport);
    netlist->getModPortMap().emplace(
        modportfullname, std::make_pair(&orig_modport.second, dest_modport));
    netlist->getSymbolTable().emplace(modportfullname, dest_modport);
    dest_modport->VpiName(orig_modport.first);
    VectorOfio_decl* ios = s.MakeIo_declVec();
    for (auto& sig : orig_modport.second.getPorts()) {
      const FileContent* const fC = sig.getFileContent();
      const NodeId nodeId = sig.getNodeId();
      const std::string_view sigName = sig.getName();
      io_decl* io = s.MakeIo_decl();
      io->VpiName(sigName);
      io->VpiParent(dest_modport);
      uint32_t direction = UhdmWriter::getVpiDirection(sig.getDirection());
      io->VpiDirection(direction);
      fC->populateCoreMembers(nodeId, nodeId, io);
      any* net = bind_net_(interf_instance, sigName);
      if (net == nullptr) {
        net = bind_net_(instance, sigName);
      }
      if (net && (net->UhdmType() == uhdminterface_inst)) {
        ref_obj* n = s.MakeRef_obj();
        n->VpiName(sigName);
        n->VpiFullName(StrCat(instance->getFullPathName(), ".", sigName));
        fC->populateCoreMembers(nodeId, nodeId, n);
        if (sigName != instName)  // prevent loop in listener
          n->Actual_group(net);
        net = n;
        io->Expr(net);
      } else {
        m_helper.setParentNoOverride(net, io);
        io->Expr(net);
      }
      ios->push_back(io);
    }
    dest_modport->Io_decls(ios);
    dest_modports->push_back(dest_modport);
  }
  sm->Modports(dest_modports);
  if (Netlist* netl = interf_instance->getNetlist()) {
    if (auto vars = netl->variables()) {
      sm->Variables(vars);
      for (auto v : *vars) {
        v->VpiParent(sm);
      }
    }
    if (auto vars = netl->ports()) {
      sm->Ports(vars);
      for (auto v : *vars) {
        v->VpiParent(sm);
      }
    }
  }
  return sm;
}

modport* NetlistElaboration::elab_modport_(
    ModuleInstance* instance, ModuleInstance* interfaceInstance,
    std::string_view instName, std::string_view defName, ModuleDefinition* mod,
    PathId fileId, uint32_t lineNb, std::string_view modPortName,
    UHDM::interface_array* interf_array) {
  Netlist* netlist = instance->getNetlist();
  std::string fullname = StrCat(instName, ".", modPortName);
  Netlist::ModPortMap::iterator itr = netlist->getModPortMap().find(fullname);
  if (itr == netlist->getModPortMap().end()) {
    elab_interface_(instance, interfaceInstance, instName, defName, mod, fileId,
                    lineNb, interf_array, fullname);
  }
  itr = netlist->getModPortMap().find(fullname);
  if (itr != netlist->getModPortMap().end()) {
    return (*itr).second.second;
  }
  return nullptr;
}

bool NetlistElaboration::elab_generates_(ModuleInstance* instance) {
  Serializer& s = m_compileDesign->getSerializer();
  Netlist* netlist = instance->getNetlist();
  DesignComponent* comp_def = instance->getDefinition();
  if (ModuleDefinition* mm =
          valuedcomponenti_cast<ModuleDefinition*>(comp_def)) {
    VObjectType insttype = instance->getType();
    if (insttype == VObjectType::paConditional_generate_construct ||
        insttype == VObjectType::paLoop_generate_construct ||
        insttype == VObjectType::paGenerate_begin_end_block ||
        insttype == VObjectType::paGenerate_item ||
        insttype == VObjectType::paGenerate_region ||
        insttype == VObjectType::paGenerate_module_conditional_statement ||
        insttype == VObjectType::paGenerate_interface_conditional_statement ||
        insttype == VObjectType::paGenerate_module_loop_statement ||
        insttype == VObjectType::paGenerate_interface_loop_statement ||
        insttype == VObjectType::paGenerate_module_named_block ||
        insttype == VObjectType::paGenerate_interface_named_block ||
        insttype == VObjectType::paGenerate_module_block ||
        insttype == VObjectType::paGenerate_interface_block ||
        insttype == VObjectType::paGenerate_module_item ||
        insttype == VObjectType::paGenerate_interface_item) {
      std::vector<gen_scope_array*>* gen_scopes = netlist->gen_scopes();
      if (gen_scopes == nullptr) {
        gen_scopes = s.MakeGen_scope_arrayVec();
        netlist->gen_scopes(gen_scopes);
      }

      const FileContent* fC = mm->getFileContents()[0];
      gen_scope_array* gen_scope_array = s.MakeGen_scope_array();
      std::vector<gen_scope*>* vec = s.MakeGen_scopeVec();
      gen_scope* gen_scope = s.MakeGen_scope();
      vec->push_back(gen_scope);
      gen_scope_array->Gen_scopes(vec);
      fC->populateCoreMembers(mm->getGenBlockId(), mm->getGenBlockId(),
                              gen_scope);
      gen_scope->VpiName(instance->getInstanceName());
      fC->populateCoreMembers(mm->getGenBlockId(), mm->getGenBlockId(),
                              gen_scope_array);
      gen_scopes->push_back(gen_scope_array);

      if (mm->getContAssigns()) gen_scope->Cont_assigns(mm->getContAssigns());
      if (mm->getProcesses()) gen_scope->Process(mm->getProcesses());
      if (mm->getParameters()) gen_scope->Parameters(mm->getParameters());
      if (mm->getParam_assigns())
        gen_scope->Param_assigns(mm->getParam_assigns());

      elab_ports_nets_(instance, true);
      elab_ports_nets_(instance, false);

      gen_scope->Nets(netlist->nets());
      gen_scope->Array_vars(netlist->array_vars());
    }
  }
  return true;
}

bool NetlistElaboration::elab_interfaces_(ModuleInstance* instance) {
  for (uint32_t i = 0; i < instance->getNbChildren(); i++) {
    ModuleInstance* child = instance->getChildren(i);
    Netlist* netlist = child->getNetlist();
    if (netlist == nullptr) {
      netlist = new Netlist(child);
      child->setNetlist(netlist);
    }
    DesignComponent* childDef = child->getDefinition();
    if (ModuleDefinition* mm =
            valuedcomponenti_cast<ModuleDefinition*>(childDef)) {
      VObjectType insttype = child->getType();
      if (insttype == VObjectType::paInterface_instantiation) {
        elab_interface_(instance, child, child->getInstanceName(),
                        child->getModuleName(), mm, child->getFileId(),
                        child->getLineNb(), nullptr, "");
      }
    }
  }

  return true;
}

bool NetlistElaboration::elab_ports_nets_(ModuleInstance* instance,
                                          bool ports) {
  Netlist* netlist = instance->getNetlist();
  DesignComponent* comp = instance->getDefinition();
  if (comp == nullptr) {
    return true;
  }
  return elab_ports_nets_(instance, instance, netlist, netlist, comp, "",
                          ports);
}

bool NetlistElaboration::elabSignal(Signal* sig, ModuleInstance* instance,
                                    ModuleInstance* child,
                                    Netlist* parentNetlist, Netlist* netlist,
                                    DesignComponent* comp,
                                    std::string_view prefix, bool signalIsPort,
                                    TypespecCache& tscache, Reduce reduce) {
  Serializer& s = m_compileDesign->getSerializer();
  std::vector<net*>* nets = netlist->nets();
  std::vector<variables*>* vars = netlist->variables();
  std::vector<array_net*>* array_nets = netlist->array_nets();
  const FileContent* fC = sig->getFileContent();
  NodeId id = sig->getNodeId();
  NodeId packedDimension = sig->getPackedDimension();
  NodeId unpackedDimension = sig->getUnpackedDimension();
  // Nets pass
  const DataType* dtype = sig->getDataType();
  VObjectType subnettype = sig->getType();
  // For typed net declarations (e.g. "wand integer"), the original net keyword
  // (paNetType_Wand/Wor/Wire) is preserved in getSubNetType(). The m_type
  // (subnettype) holds the data type which may have overridden the net keyword.
  VObjectType netKeyword = sig->getSubNetType();
  UHDM::typespec* tps = nullptr;
  // Determine if the "signal" is a net or a var
  bool isNet = true;
  if ((dtype && (subnettype == VObjectType::slNoType)) || sig->isConst() ||
      sig->isVar() || (!sig->isStatic()) ||
      (subnettype == VObjectType::paClass_scope) ||
      (subnettype == VObjectType::slStringConst) ||
      (subnettype == VObjectType::paIntegerAtomType_Int) ||
      (subnettype == VObjectType::paIntegerAtomType_Integer) ||
      (subnettype == VObjectType::paIntegerAtomType_Byte) ||
      (subnettype == VObjectType::paIntegerAtomType_LongInt) ||
      (subnettype == VObjectType::paIntegerAtomType_Shortint) ||
      (subnettype == VObjectType::paString_type) ||
      (subnettype == VObjectType::paNonIntType_Real) ||
      (subnettype == VObjectType::paNonIntType_RealTime) ||
      (subnettype == VObjectType::paNonIntType_ShortReal) ||
      (subnettype == VObjectType::paEvent_type) ||
      (subnettype == VObjectType::paChandle_type) ||
      (subnettype == VObjectType::paIntVec_TypeBit) ||
      (subnettype == VObjectType::paEnum_base_type) ||
      ((!sig->isVar()) && (subnettype == VObjectType::paIntVec_TypeLogic))) {
    isNet = false;
  }
  if (sig->getDirection() == VObjectType::paPortDir_Out ||
      sig->getDirection() == VObjectType::paPortDir_Inp ||
      sig->getDirection() == VObjectType::paPortDir_Inout) {
    if ((!sig->isVar()) && (subnettype == VObjectType::paIntVec_TypeLogic)) {
      isNet = true;
    }
  }
  // Typed net declarations like "wand integer" or "wand typename" store the
  // original net keyword in getSubNetType(). Override isNet for these cases.
  if (netKeyword != VObjectType::slNoType) {
    isNet = true;
  }

  NodeId typeSpecId = sig->getTypeSpecId();
  if (typeSpecId) {
    auto itr = tscache.find(typeSpecId);
    if (itr == tscache.end()) {
      m_helper.checkForLoops(true);
      tps = m_helper.compileTypespec(comp, fC, typeSpecId, m_compileDesign,
                                     reduce, nullptr, child, true);
      m_helper.checkForLoops(false);
      tscache.emplace(typeSpecId, tps);
    } else {
      tps = (*itr).second;
    }
  }
  if (tps == nullptr) {
    if (sig->getInterfaceTypeNameId()) {
      auto itr = tscache.find(sig->getInterfaceTypeNameId());
      if (itr == tscache.end()) {
        m_helper.checkForLoops(true);
        tps = m_helper.compileTypespec(comp, fC, sig->getInterfaceTypeNameId(),
                                       m_compileDesign, reduce, nullptr, child,
                                       true);
        m_helper.checkForLoops(false);
        tscache.emplace(sig->getInterfaceTypeNameId(), tps);
      } else {
        tps = (*itr).second;
      }
    }
  }
  if (tps) {
    typespec* tmp = tps;
    UHDM_OBJECT_TYPE ttmp = tmp->UhdmType();
    if (ttmp == uhdmpacked_array_typespec) {
      if (ref_typespec* ert = ((packed_array_typespec*)tmp)->Elem_typespec()) {
        tmp = ert->Actual_typespec();
      }
    } else if (ttmp == uhdmstruct_typespec) {
      struct_typespec* the_tps = (struct_typespec*)tmp;
      if (the_tps->Members()) {
        isNet = true;
        for (typespec_member* member : *the_tps->Members()) {
          if (const typespec* mtps = member->Typespec()->Actual_typespec()) {
            UHDM_OBJECT_TYPE mtype = mtps->UhdmType();
            if (mtype != uhdmlogic_typespec && mtype != uhdmstruct_typespec) {
              isNet = false;
              break;
            }
          }
        }
      }
    } else if (ttmp == uhdmenum_typespec) {
      isNet = false;
    } else if (ttmp == uhdmbit_typespec) {
      isNet = false;
    } else if (ttmp == uhdmbyte_typespec) {
      isNet = false;
    } else if (ttmp == uhdmreal_typespec) {
      isNet = false;
    } else if (ttmp == uhdmclass_typespec) {
      isNet = false;
    } else if (ttmp == uhdminterface_typespec) {
      if (!signalIsPort) {
        SymbolTable* symbols = m_compileDesign->getCompiler()->getSymbolTable();
        ErrorContainer* errors =
            m_compileDesign->getCompiler()->getErrorContainer();
        Location loc1(fC->getFileId(), fC->Line(id), fC->Column(id),
                      symbols->registerSymbol(sig->getName()));
        Error err(ErrorDefinition::ELAB_USE_INTERFACE_AS_SIGNAL_TYPE, loc1);
        errors->addError(err);
      }
      // Don't create a signal
      return isNet;
    }
  }

  if (!isNet) {
    if (vars == nullptr) {
      vars = s.MakeVariablesVec();
      netlist->variables(vars);
    }
  }

  const std::string_view signame = sig->getName();
  const std::string parentSymbol = StrCat(prefix, signame);

  // Packed and unpacked ranges
  int32_t packedSize;
  int32_t unpackedSize;
  m_helper.checkForLoops(true);
  std::vector<UHDM::range*>* packedDimensions =
      m_helper.compileRanges(comp, fC, packedDimension, m_compileDesign, reduce,
                             nullptr, child, packedSize, false);
  m_helper.checkForLoops(false);
  m_helper.checkForLoops(true);
  std::vector<UHDM::range*>* unpackedDimensions =
      m_helper.compileRanges(comp, fC, unpackedDimension, m_compileDesign,
                             reduce, nullptr, child, unpackedSize, false);
  m_helper.checkForLoops(false);
  any* obj = nullptr;

  // Assignment to a default value
  expr* exp = exprFromAssign_(comp, fC, id, unpackedDimension, child);
  if ((exp == nullptr) && sig->getDefaultValue()) {
    m_helper.checkForLoops(true);
    exp = (expr*)m_helper.compileExpression(comp, fC, sig->getDefaultValue(),
                                            m_compileDesign, reduce, nullptr,
                                            child);
    m_helper.checkForLoops(false);
  }
  if (isNet) {
    // Nets
    if (dtype) {
      dtype = dtype->getActual();
      if (const DummyType* en = datatype_cast<const DummyType*>(dtype)) {
        UHDM::typespec* spec = en->getTypespec();
        if (spec->UhdmType() == uhdmlogic_typespec) {
          logic_net* logicn = s.MakeLogic_net();
          if (sig->attributes()) {
            logicn->Attributes(sig->attributes());
            for (auto a : *sig->attributes()) a->VpiParent(logicn);
          }
          logicn->VpiSigned(sig->isSigned());
          logicn->VpiNetType(UhdmWriter::getVpiNetType(netKeyword != VObjectType::slNoType ? netKeyword : sig->getType()));
          // Move range to typespec for simple types
          // logicn->Ranges(packedDimensions);
          ref_typespec* rt = s.MakeRef_typespec();
          rt->VpiParent(logicn);
          rt->Actual_typespec(spec);
          logicn->Typespec(rt);
          logicn->VpiName(signame);
          spec->VpiParent(logicn);
          obj = logicn;
        } else if (spec->UhdmType() == uhdmstruct_typespec) {
          struct_net* stv = s.MakeStruct_net();
          if (sig->attributes()) {
            stv->Attributes(sig->attributes());
            for (auto a : *sig->attributes()) a->VpiParent(stv);
          }
          ref_typespec* rt = s.MakeRef_typespec();
          rt->VpiParent(stv);
          rt->Actual_typespec(spec);
          stv->Typespec(rt);
          spec->VpiParent(stv);
          obj = stv;
          if (packedDimensions) {
            packed_array_net* pnets = s.MakePacked_array_net();
            pnets->Ranges(packedDimensions);
            pnets->Elements(s.MakeAnyVec());
            pnets->Elements()->push_back(stv);
            stv->VpiParent(pnets);
            for (auto r : *packedDimensions) r->VpiParent(pnets);
            obj = pnets;
          }
        } else if (spec->UhdmType() == uhdmenum_typespec) {
          enum_net* stv = s.MakeEnum_net();
          if (sig->attributes()) {
            stv->Attributes(sig->attributes());
            for (auto a : *sig->attributes()) a->VpiParent(stv);
          }
          ref_typespec* rt = s.MakeRef_typespec();
          rt->VpiParent(stv);
          rt->Actual_typespec(spec);
          stv->Typespec(rt);
          spec->VpiParent(stv);
          obj = stv;
          if (packedDimensions) {
            packed_array_net* pnets = s.MakePacked_array_net();
            pnets->Ranges(packedDimensions);
            pnets->Elements(s.MakeAnyVec());
            pnets->Elements()->push_back(stv);
            stv->VpiParent(pnets);
            for (auto r : *packedDimensions) r->VpiParent(pnets);
            obj = pnets;
          }
        } else if (spec->UhdmType() == uhdmbit_typespec) {
          bit_var* logicn = s.MakeBit_var();
          if (sig->attributes()) {
            logicn->Attributes(sig->attributes());
            for (auto a : *sig->attributes()) a->VpiParent(logicn);
          }
          logicn->VpiSigned(sig->isSigned());
          // Move range to typespec for simple types
          // logicn->Ranges(packedDimensions);
          ref_typespec* rt = s.MakeRef_typespec();
          rt->VpiParent(logicn);
          rt->Actual_typespec(spec);
          logicn->Typespec(rt);
          logicn->VpiName(signame);
          spec->VpiParent(logicn);
          obj = logicn;
        } else if (spec->UhdmType() == uhdmbyte_typespec) {
          byte_var* logicn = s.MakeByte_var();
          if (sig->attributes()) {
            logicn->Attributes(sig->attributes());
            for (auto a : *sig->attributes()) a->VpiParent(logicn);
          }
          logicn->VpiSigned(sig->isSigned());
          logicn->VpiName(signame);
          ref_typespec* rt = s.MakeRef_typespec();
          rt->VpiParent(logicn);
          rt->Actual_typespec(spec);
          logicn->Typespec(rt);
          spec->VpiParent(logicn);
          obj = logicn;
        } else {
          variables* var = m_helper.getSimpleVarFromTypespec(
              spec, packedDimensions, m_compileDesign);
          if (sig->attributes()) {
            var->Attributes(sig->attributes());
            for (auto a : *sig->attributes()) a->VpiParent(var);
          }
          var->Expr(exp);
          var->VpiConstantVariable(sig->isConst());
          var->VpiSigned(sig->isSigned());
          var->VpiName(signame);
          exp->VpiParent(var);
          obj = var;
        }
      } else if (const Enum* en = datatype_cast<const Enum*>(dtype)) {
        enum_net* stv = s.MakeEnum_net();
        stv->VpiName(signame);
        ref_typespec* rt = s.MakeRef_typespec();
        rt->VpiParent(stv);
        rt->Actual_typespec(en->getTypespec());
        stv->Typespec(rt);
        if (sig->attributes()) {
          stv->Attributes(sig->attributes());
          for (auto a : *sig->attributes()) a->VpiParent(stv);
        }
        obj = stv;
        if (packedDimensions) {
          packed_array_net* pnets = s.MakePacked_array_net();
          pnets->Ranges(packedDimensions);
          pnets->Elements(s.MakeAnyVec());
          pnets->Elements()->push_back(stv);
          stv->VpiParent(pnets);
          for (auto r : *packedDimensions) r->VpiParent(pnets);
          obj = pnets;
          pnets->VpiNetType(UhdmWriter::getVpiNetType(netKeyword != VObjectType::slNoType ? netKeyword : sig->getType()));
        } else {
          stv->VpiNetType(UhdmWriter::getVpiNetType(netKeyword != VObjectType::slNoType ? netKeyword : sig->getType()));
        }
      } else if (const Struct* st = datatype_cast<const Struct*>(dtype)) {
        struct_net* stv = s.MakeStruct_net();
        stv->VpiName(signame);
        if (sig->attributes()) {
          stv->Attributes(sig->attributes());
          for (auto a : *sig->attributes()) a->VpiParent(stv);
        }
        ref_typespec* rt = s.MakeRef_typespec();
        rt->VpiParent(stv);
        rt->Actual_typespec(st->getTypespec());
        stv->Typespec(rt);
        obj = stv;
        if (packedDimensions) {
          packed_array_net* pnets = s.MakePacked_array_net();
          pnets->Ranges(packedDimensions);
          pnets->Elements(s.MakeAnyVec());
          pnets->Elements()->push_back(stv);
          stv->VpiParent(pnets);
          for (auto r : *packedDimensions) r->VpiParent(pnets);
          obj = pnets;
          pnets->VpiNetType(UhdmWriter::getVpiNetType(netKeyword != VObjectType::slNoType ? netKeyword : sig->getType()));
        } else {
          stv->VpiNetType(UhdmWriter::getVpiNetType(netKeyword != VObjectType::slNoType ? netKeyword : sig->getType()));
        }
      } else if (dtype->getCategory() == DataType::Category::PARAMETER ||
                 dtype->getCategory() == DataType::Category::SIMPLE_TYPEDEF) {
        UHDM::typespec* spec = nullptr;
        if (dtype->getCategory() == DataType::Category::SIMPLE_TYPEDEF) {
          const SimpleType* sit = datatype_cast<const SimpleType*>(dtype);
          spec = sit->getTypespec();
        } else {
          const Parameter* param = datatype_cast<const Parameter*>(dtype);
          spec = param->getTypespec();
          if (spec == nullptr) {
            spec = tps;
          }
        }
        if (spec->UhdmType() == uhdmlogic_typespec) {
          logic_net* logicn = s.MakeLogic_net();
          if (sig->attributes()) {
            logicn->Attributes(sig->attributes());
            for (auto a : *sig->attributes()) a->VpiParent(logicn);
          }
          logicn->VpiSigned(sig->isSigned());
          logicn->VpiNetType(UhdmWriter::getVpiNetType(netKeyword != VObjectType::slNoType ? netKeyword : sig->getType()));
          // Move range to typespec for simple types
          // logicn->Ranges(packedDimensions);
          ref_typespec* rt = s.MakeRef_typespec();
          rt->VpiParent(logicn);
          rt->Actual_typespec(spec);
          logicn->Typespec(rt);
          spec->VpiParent(logicn);
          logicn->VpiName(signame);
          obj = logicn;
        } else if (spec->UhdmType() == uhdmstruct_typespec) {
          struct_net* stv = s.MakeStruct_net();
          stv->VpiName(signame);
          if (sig->attributes()) {
            stv->Attributes(sig->attributes());
            for (auto a : *sig->attributes()) a->VpiParent(stv);
          }
          ref_typespec* rt = s.MakeRef_typespec();
          rt->VpiParent(stv);
          rt->Actual_typespec(spec);
          stv->Typespec(rt);
          spec->VpiParent(stv);
          obj = stv;
          if (packedDimensions) {
            packed_array_net* pnets = s.MakePacked_array_net();
            pnets->Ranges(packedDimensions);
            pnets->Elements(s.MakeAnyVec());
            pnets->Elements()->push_back(stv);
            stv->VpiParent(pnets);
            for (auto r : *packedDimensions) r->VpiParent(pnets);
            obj = pnets;
            pnets->VpiNetType(UhdmWriter::getVpiNetType(netKeyword != VObjectType::slNoType ? netKeyword : sig->getType()));
          } else {
            stv->VpiNetType(UhdmWriter::getVpiNetType(netKeyword != VObjectType::slNoType ? netKeyword : sig->getType()));
          }
        } else if (spec->UhdmType() == uhdmenum_typespec) {
          enum_net* stv = s.MakeEnum_net();
          stv->VpiName(signame);
          if (sig->attributes()) {
            stv->Attributes(sig->attributes());
            for (auto a : *sig->attributes()) a->VpiParent(stv);
          }
          ref_typespec* rt = s.MakeRef_typespec();
          rt->VpiParent(stv);
          rt->Actual_typespec(spec);
          stv->Typespec(rt);
          spec->VpiParent(stv);
          obj = stv;
          if (packedDimensions) {
            packed_array_net* pnets = s.MakePacked_array_net();
            pnets->Ranges(packedDimensions);
            pnets->Elements(s.MakeAnyVec());
            pnets->Elements()->push_back(stv);
            stv->VpiParent(pnets);
            for (auto r : *packedDimensions) r->VpiParent(pnets);
            obj = pnets;
            pnets->VpiNetType(UhdmWriter::getVpiNetType(netKeyword != VObjectType::slNoType ? netKeyword : sig->getType()));
          } else {
            stv->VpiNetType(UhdmWriter::getVpiNetType(netKeyword != VObjectType::slNoType ? netKeyword : sig->getType()));
          }
        } else if (spec->UhdmType() == uhdmbit_typespec) {
          bit_var* logicn = s.MakeBit_var();
          if (sig->attributes()) {
            logicn->Attributes(sig->attributes());
            for (auto a : *sig->attributes()) a->VpiParent(logicn);
          }
          logicn->VpiSigned(sig->isSigned());
          ref_typespec* rt = s.MakeRef_typespec();
          rt->VpiParent(logicn);
          rt->Actual_typespec(spec);
          logicn->Typespec(rt);
          spec->VpiParent(logicn);
          // Move range to typespec for simple types
          // logicn->Ranges(packedDimensions);
          logicn->VpiName(signame);
          obj = logicn;
        } else if (spec->UhdmType() == uhdmbyte_typespec) {
          byte_var* logicn = s.MakeByte_var();
          if (sig->attributes()) {
            logicn->Attributes(sig->attributes());
            for (auto a : *sig->attributes()) a->VpiParent(logicn);
          }
          logicn->VpiSigned(sig->isSigned());
          logicn->VpiName(signame);
          ref_typespec* rt = s.MakeRef_typespec();
          rt->VpiParent(logicn);
          rt->Actual_typespec(spec);
          logicn->Typespec(rt);
          spec->VpiParent(logicn);
          obj = logicn;
        } else {
          variables* var = m_helper.getSimpleVarFromTypespec(
              spec, packedDimensions, m_compileDesign);
          if (sig->attributes()) {
            var->Attributes(sig->attributes());
            for (auto a : *sig->attributes()) a->VpiParent(var);
          }
          var->Expr(exp);
          var->VpiConstantVariable(sig->isConst());
          var->VpiSigned(sig->isSigned());
          var->VpiName(signame);
          exp->VpiParent(var);
          obj = var;
        }
      } else {
        logic_net* logicn = s.MakeLogic_net();
        if (sig->attributes()) {
          logicn->Attributes(sig->attributes());
          for (auto a : *sig->attributes()) a->VpiParent(logicn);
        }
        logicn->VpiSigned(sig->isSigned());
        logicn->VpiNetType(UhdmWriter::getVpiNetType(netKeyword != VObjectType::slNoType ? netKeyword : sig->getType()));
        ref_typespec* rt = s.MakeRef_typespec();
        rt->VpiParent(logicn);
        rt->Actual_typespec(tps);
        logicn->Typespec(rt);
        tps->VpiParent(logicn);
        // Move range to typespec for simple types
        // logicn->Ranges(packedDimensions);
        logicn->VpiName(signame);
        obj = logicn;
      }

      if (unpackedDimensions) {
        array_net* array_net = s.MakeArray_net();
        array_net->Nets(s.MakeNetVec());
        array_net->Ranges(unpackedDimensions);
        array_net->VpiName(signame);
        array_net->VpiSize(unpackedSize);
        for (auto r : *unpackedDimensions) r->VpiParent(array_net);
        fC->populateCoreMembers(sig->getNodeId(), sig->getNodeId(), array_net);
        if (array_nets == nullptr) {
          array_nets = s.MakeArray_netVec();
          netlist->array_nets(array_nets);
        }
        array_nets->push_back(array_net);
        obj->VpiParent(array_net);
        UHDM::VectorOfnet* array_n = array_net->Nets();
        array_n->push_back((net*)obj);
        array_net->Attributes(((net*)obj)->Attributes());
      } else {
        if (nets == nullptr) {
          nets = s.MakeNetVec();
          netlist->nets(nets);
        }
        UHDM_OBJECT_TYPE nettype = obj->UhdmType();
        if (nettype == uhdmenum_net) {
          ((enum_net*)obj)->VpiName(signame);
        } else if (nettype == uhdmstruct_net) {
          ((struct_net*)obj)->VpiName(signame);
        } else if (nettype == uhdmpacked_array_net) {
          ((packed_array_net*)obj)->VpiName(signame);
        }
        nets->push_back((net*)obj);
      }
    } else if (subnettype == VObjectType::paStruct_union) {
      // Implicit type
      struct_net* stv = s.MakeStruct_net();
      stv->VpiName(signame);
      if (sig->attributes()) {
        stv->Attributes(sig->attributes());
        for (auto a : *sig->attributes()) a->VpiParent(stv);
      }
      ref_typespec* rt = s.MakeRef_typespec();
      rt->VpiParent(stv);
      rt->Actual_typespec(tps);
      stv->Typespec(rt);
      tps->VpiParent(stv);
      obj = stv;
      stv->VpiName(signame);
      if (nets == nullptr) {
        nets = s.MakeNetVec();
        netlist->nets(nets);
      }
      nets->push_back(stv);
    } else if (tps && tps->UhdmType() == uhdmstruct_typespec) {
      struct_net* stv = s.MakeStruct_net();
      stv->VpiName(signame);
      ref_typespec* rt = s.MakeRef_typespec();
      rt->VpiParent(stv);
      rt->Actual_typespec(tps);
      stv->Typespec(rt);
      tps->VpiParent(stv);
      obj = stv;
      if (unpackedDimensions) {
        array_net* array_net = s.MakeArray_net();
        array_net->Nets(s.MakeNetVec());
        array_net->Ranges(unpackedDimensions);
        array_net->VpiName(signame);
        array_net->VpiSize(unpackedSize);
        for (auto r : *unpackedDimensions) r->VpiParent(array_net);
        fC->populateCoreMembers(sig->getNodeId(), sig->getNodeId(), array_net);
        if (array_nets == nullptr) {
          array_nets = s.MakeArray_netVec();
          netlist->array_nets(array_nets);
        }
        array_nets->push_back(array_net);
        obj->VpiParent(array_net);
        UHDM::VectorOfnet* array_n = array_net->Nets();
        array_n->push_back((net*)obj);
        array_net->Attributes(((net*)obj)->Attributes());
      } else {
        if (nets == nullptr) {
          nets = s.MakeNetVec();
          netlist->nets(nets);
        }
        if (obj->UhdmType() == uhdmenum_net) {
          ((enum_net*)obj)->VpiName(signame);
        } else if (obj->UhdmType() == uhdmstruct_net) {
          ((struct_net*)obj)->VpiName(signame);
        }
        nets->push_back((net*)obj);
      }
    } else {
      logic_net* logicn = s.MakeLogic_net();
      logicn->VpiSigned(sig->isSigned());
      logicn->VpiNetType(UhdmWriter::getVpiNetType(netKeyword != VObjectType::slNoType ? netKeyword : sig->getType()));
      if (sig->attributes()) {
        logicn->Attributes(sig->attributes());
        for (auto a : *sig->attributes()) a->VpiParent(logicn);
      }
      if (tps != nullptr) {
        // Move range to typespec for simple types
        // logicn->Ranges(packedDimensions);
        ref_typespec* rt = s.MakeRef_typespec();
        rt->VpiParent(logicn);
        rt->Actual_typespec(tps);
        logicn->Typespec(rt);
        tps->VpiParent(logicn);
      }
      if (unpackedDimensions) {
        fC->populateCoreMembers(id, id, logicn);
        array_net* array_net = s.MakeArray_net();
        array_net->Nets(s.MakeNetVec());
        array_net->Ranges(unpackedDimensions);
        array_net->VpiName(signame);
        array_net->VpiSize(unpackedSize);
        for (auto r : *unpackedDimensions) r->VpiParent(array_net);
        fC->populateCoreMembers(sig->getNodeId(), sig->getNodeId(), array_net);
        if (array_nets == nullptr) {
          array_nets = s.MakeArray_netVec();
          netlist->array_nets(array_nets);
        }
        array_nets->push_back(array_net);
        logicn->VpiParent(array_net);
        UHDM::VectorOfnet* array_n = array_net->Nets();
        array_n->push_back(logicn);
        obj = array_net;
        array_net->Attributes(((net*)logicn)->Attributes());
      } else {
        logicn->VpiName(signame);
        logicn->VpiSigned(sig->isSigned());
        obj = logicn;
        if (nets == nullptr) {
          nets = s.MakeNetVec();
          netlist->nets(nets);
        }
        nets->push_back(logicn);
      }
    }
    if (parentNetlist)
      parentNetlist->getSymbolTable().emplace(parentSymbol, obj);
    if (netlist) netlist->getSymbolTable().emplace(signame, obj);

    if (exp && ((!signalIsPort) ||
                (signalIsPort &&
                 (sig->getDirection() != VObjectType::paPortDir_Out)))) {
      // Cont assign for input port
      cont_assign* assign = s.MakeCont_assign();
      assign->VpiNetDeclAssign(true);
      fC->populateCoreMembers(id, id, assign);
      assign->Lhs((expr*)obj);
      assign->Rhs(exp);
      m_helper.setParentNoOverride((expr*)obj, assign);
      m_helper.setParentNoOverride(exp, assign);
      if (sig->getDelay()) {
        m_helper.checkForLoops(true);
        if (expr* delay_expr = (expr*)m_helper.compileExpression(
                comp, fC, sig->getDelay(), m_compileDesign, reduce, assign,
                child)) {
          assign->Delay(delay_expr);
        }
        m_helper.checkForLoops(false);
      }
      std::vector<cont_assign*>* assigns = netlist->cont_assigns();
      if (assigns == nullptr) {
        netlist->cont_assigns(s.MakeCont_assignVec());
        assigns = netlist->cont_assigns();
      }
      assigns->push_back(assign);
    } else if (exp && signalIsPort &&
               (sig->getDirection() == VObjectType::paPortDir_Out)) {
      // Initial statement for output port
      initial* init = s.MakeInitial();
      UHDM::VectorOfprocess_stmt* processes = netlist->process_stmts();
      if (processes == nullptr) {
        netlist->process_stmts(s.MakeProcess_stmtVec());
        processes = netlist->process_stmts();
      }
      netlist->process_stmts()->push_back(init);
      UHDM::assignment* assign_stmt = s.MakeAssignment();
      init->Stmt(assign_stmt);
      UHDM::ref_obj* ref = s.MakeRef_obj();
      ref->VpiName(sig->getName());
      ref->VpiParent(assign_stmt);
      fC->populateCoreMembers(sig->getNodeId(), sig->getNodeId(), ref);
      assign_stmt->Lhs(ref);
      fC->populateCoreMembers(id, id, assign_stmt);
      assign_stmt->VpiParent(init);
      assign_stmt->Rhs(exp);
    }
  } else {
    // Vars
    obj = makeVar_(comp, sig, packedDimensions, packedSize, unpackedDimensions,
                   unpackedSize, child, vars, exp, tps);
  }

  if (obj) {
    if (obj->VpiLineNo() == 0) {
      if (unpackedDimension) {
        fC->populateCoreMembers(id, unpackedDimension, obj);
      } else {
        fC->populateCoreMembers(id, id, obj);
      }
    }
    if (parentNetlist)
      parentNetlist->getSymbolTable().emplace(parentSymbol, obj);
    netlist->getSymbolTable().emplace(signame, obj);
  } else {
    // Unsupported type
    ErrorContainer* errors =
        m_compileDesign->getCompiler()->getErrorContainer();
    SymbolTable* symbols = m_compileDesign->getCompiler()->getSymbolTable();
    Location loc(fC->getFileId(), fC->Line(id), fC->Column(id),
                 symbols->registerSymbol(signame));
    Error err(ErrorDefinition::UHDM_UNSUPPORTED_SIGNAL, loc);
    errors->addError(err);
  }
  return isNet;
}

bool NetlistElaboration::elab_ports_nets_(
    ModuleInstance* instance, ModuleInstance* child, Netlist* parentNetlist,
    Netlist* netlist, DesignComponent* comp, std::string_view prefix,
    bool do_ports) {
  Serializer& s = m_compileDesign->getSerializer();
  VObjectType compType = comp->getType();
  std::vector<port*>* ports = netlist->ports();
  TypespecCache tscache;
  std::set<std::string_view> portInterf;
  for (int32_t pass = 0; pass < 3; pass++) {
    std::vector<Signal*>* signals = nullptr;
    if (compType == VObjectType::paModule_declaration ||
        compType == VObjectType::paConditional_generate_construct ||
        compType == VObjectType::paLoop_generate_construct ||
        compType == VObjectType::paGenerate_item ||
        compType == VObjectType::paGenerate_region ||
        compType == VObjectType::paGenerate_module_conditional_statement ||
        compType == VObjectType::paGenerate_interface_conditional_statement ||
        compType == VObjectType::paGenerate_module_loop_statement ||
        compType == VObjectType::paGenerate_interface_loop_statement ||
        compType == VObjectType::paGenerate_module_named_block ||
        compType == VObjectType::paGenerate_interface_named_block ||
        compType == VObjectType::paGenerate_module_block ||
        compType == VObjectType::paGenerate_interface_block ||
        compType == VObjectType::paGenerate_module_item ||
        compType == VObjectType::paGenerate_interface_item ||
        compType == VObjectType::paGenerate_begin_end_block ||
        compType == VObjectType::paInterface_declaration ||
        compType == VObjectType::paProgram_declaration) {
      if (pass == 1)
        signals = &comp->getSignals();
      else
        signals = &comp->getPorts();
    } else {
      continue;
    }
    int32_t portIndex = 0;
    int32_t lastPortDirection = vpiInout;
    for (Signal* sig : *signals) {
      const FileContent* fC = sig->getFileContent();
      NodeId id = sig->getNodeId();
      if (pass == 0) {
        if (!do_ports) continue;
        // Ports pass
        port* dest_port = s.MakePort();
        if (sig->getDirection() != VObjectType::slNoType) {
          lastPortDirection = UhdmWriter::getVpiDirection(sig->getDirection());
        }
        dest_port->VpiDirection(lastPortDirection);
        std::string signame;
        VObjectType nodeIdType = fC->Type(sig->getNodeId());
        if (nodeIdType == VObjectType::slStringConst) {
          signame = sig->getName();
          dest_port->VpiName(signame);
        } else if (nodeIdType == VObjectType::paPort) {
          NodeId PortName = fC->Child(sig->getNodeId());
          signame = fC->SymName(PortName);
          dest_port->VpiName(signame);
          NodeId Port_expr = fC->Sibling(PortName);
          if (fC->Type(Port_expr) == VObjectType::paPort_expression) {
            m_helper.checkForLoops(true);
            any* exp =
                m_helper.compileExpression(comp, fC, Port_expr, m_compileDesign,
                                           Reduce::Yes, nullptr, child, false);
            m_helper.checkForLoops(false);
            dest_port->Low_conn(exp);
          }
        }
        fC->populateCoreMembers(id, id, dest_port);
        if (ports == nullptr) {
          ports = s.MakePortVec();
          netlist->ports(ports);
        }
        ports->push_back(dest_port);

        NodeId unpackedDimension = sig->getUnpackedDimension();
        int32_t unpackedSize;
        m_helper.checkForLoops(true);
        std::vector<UHDM::range*>* unpackedDimensions = m_helper.compileRanges(
            comp, fC, unpackedDimension, m_compileDesign, Reduce::Yes, nullptr,
            child, unpackedSize, false);
        m_helper.checkForLoops(false);
        NodeId typeSpecId = sig->getTypeSpecId();
        if (typeSpecId) {
          UHDM::typespec* tps = nullptr;
          auto itr = tscache.find(typeSpecId);
          if (itr == tscache.end()) {
            m_helper.checkForLoops(true);
            tps = m_helper.compileTypespec(comp, fC, typeSpecId,
                                           m_compileDesign, Reduce::Yes,
                                           dest_port, instance, true);
            m_helper.checkForLoops(false);
            tscache.emplace(typeSpecId, tps);
          } else {
            tps = (*itr).second;
          }
          if (tps) {
            if (dest_port->Typespec() == nullptr) {
              ref_typespec* rt = s.MakeRef_typespec();
              rt->VpiParent(dest_port);
              dest_port->Typespec(rt);
            }
            dest_port->Typespec()->Actual_typespec(tps);
          }
        }

        if (ModPort* orig_modport = sig->getModPort()) {
          portInterf.emplace(sig->getName());
          ref_obj* ref = s.MakeRef_obj();
          ref->VpiFullName(
              StrCat(instance->getFullPathName(), ".", sig->getName()));
          fC->populateCoreMembers(sig->getNodeId(), sig->getNodeId(), ref);
          ref->VpiParent(dest_port);
          dest_port->Low_conn(ref);
          Netlist::ModPortMap::iterator itr =
              netlist->getModPortMap().find(signame);
          if (itr == netlist->getModPortMap().end()) {
            ModuleDefinition* orig_interf = orig_modport->getParent();

            interface_array* array_int = nullptr;
            if (unpackedDimensions) {
              array_int = s.MakeInterface_array();
              VectorOfinstance* vec = s.MakeInstanceVec();
              array_int->Instances(vec);
              array_int->Ranges(unpackedDimensions);
              array_int->VpiName(signame);
              array_int->VpiSize(unpackedSize);
              fC->populateCoreMembers(sig->getNodeId(), sig->getNodeId(),
                                      array_int);

              auto array = netlist->interface_arrays();
              if (array == nullptr) {
                netlist->interface_arrays(s.MakeInterface_arrayVec());
                array = netlist->interface_arrays();
              }
              array->push_back(array_int);
              ref->Actual_group(array_int);
            }

            if (unpackedDimensions) {
              for (int32_t index = 0; index < unpackedSize; index++) {
                std::string sigName(sig->getName());

                ModuleInstance* interfaceRefInstance =
                    getInterfaceInstance_(instance, sigName);
                StrAppend(&sigName, "[", index, "]");
                ModuleInstance* interfaceInstance = new ModuleInstance(
                    orig_interf, sig->getFileContent(), sig->getNodeId(),
                    instance, sigName, orig_interf->getName());
                Netlist* netlistInterf = new Netlist(interfaceInstance);
                interfaceInstance->setNetlist(netlistInterf);
                if (interfaceRefInstance) {
                  for (auto& itr : interfaceRefInstance->getMappedValues()) {
                    interfaceInstance->setValue(itr.first, itr.second.first,
                                                m_exprBuilder,
                                                itr.second.second);
                  }
                }
                instance->addSubInstance(interfaceInstance);
                elab_modport_(instance, interfaceInstance, sigName,
                              orig_interf->getName(), orig_interf,
                              instance->getFileId(), instance->getLineNb(),
                              orig_modport->getName(), array_int);
              }
            } else {
              const std::string_view sigName = sig->getName();
              ModuleInstance* interfaceRefInstance =
                  getInterfaceInstance_(instance, sigName);

              ModuleInstance* interfaceInstance = new ModuleInstance(
                  orig_interf, sig->getFileContent(), sig->getNodeId(),
                  instance, signame, orig_interf->getName());
              Netlist* netlistInterf = new Netlist(interfaceInstance);
              interfaceInstance->setNetlist(netlistInterf);
              if (interfaceRefInstance) {
                for (auto& itr : interfaceRefInstance->getMappedValues()) {
                  interfaceInstance->setValue(itr.first, itr.second.first,
                                              m_exprBuilder, itr.second.second);
                }
              }

              modport* mp = elab_modport_(
                  instance, interfaceInstance, signame, orig_interf->getName(),
                  orig_interf, instance->getFileId(), instance->getLineNb(),
                  orig_modport->getName(), array_int);
              instance->addSubInstance(interfaceInstance);
              ref->Actual_group(mp);
            }

          } else {
            ref->Actual_group((*itr).second.second);
          }
        } else if (ModuleDefinition* orig_interf = sig->getInterfaceDef()) {
          portInterf.emplace(sig->getName());
          ref_obj* ref = s.MakeRef_obj();
          ref->VpiFullName(
              StrCat(instance->getFullPathName(), ".", sig->getName()));
          fC->populateCoreMembers(sig->getNodeId(), sig->getNodeId(), ref);
          dest_port->Low_conn(ref);
          Netlist::InstanceMap::iterator itr =
              netlist->getInstanceMap().find(signame);
          if (itr == netlist->getInstanceMap().end()) {
            ModuleInstance* interfaceInstance = new ModuleInstance(
                orig_interf, sig->getFileContent(), sig->getNodeId(), instance,
                signame, orig_interf->getName());
            Netlist* netlistInterf = new Netlist(interfaceInstance);
            interfaceInstance->setNetlist(netlistInterf);

            interface_array* array_int = nullptr;
            if (unpackedDimensions) {
              array_int = s.MakeInterface_array();
              VectorOfinstance* vec = s.MakeInstanceVec();
              array_int->Instances(vec);
              array_int->Ranges(unpackedDimensions);
              array_int->VpiName(signame);
              array_int->VpiSize(unpackedSize);

              auto array = netlist->interface_arrays();
              if (array == nullptr) {
                netlist->interface_arrays(s.MakeInterface_arrayVec());
                array = netlist->interface_arrays();
              }
              array->push_back(array_int);
              ref->Actual_group(array_int);
            }

            interface_inst* sm = elab_interface_(
                instance, interfaceInstance, signame, orig_interf->getName(),
                orig_interf, instance->getFileId(), instance->getLineNb(),
                array_int, "");

            if (unpackedDimensions) {
            } else {
              ref->Actual_group(sm);

              auto interfs = netlist->interfaces();
              if (interfs == nullptr) {
                netlist->interfaces(s.MakeInterface_instVec());
                interfs = netlist->interfaces();
              }
              interfs->push_back(sm);
            }

          } else {
            ref->Actual_group((*itr).second.second);
          }
        }

      } else if (pass == 1) {
        // Nets pass
        if (do_ports) continue;
        if (fC->Type(sig->getNodeId()) == VObjectType::slStringConst) {
          const std::string_view signame = sig->getName();
          if (portInterf.find(signame) == portInterf.end()) {
            bool sigIsPort = false;
            if (ports) {
              for (auto s : *ports) {
                if (s->VpiName() == signame) {
                  sigIsPort = true;
                }
              }
            }
            elabSignal(sig, instance, child, parentNetlist, netlist, comp,
                       prefix, sigIsPort, tscache, Reduce::Yes);
          }
        }

      } else if (pass == 2) {
        // Port low conn pass
        if (do_ports) continue;
        std::string signame;
        if (fC->Type(sig->getNodeId()) == VObjectType::slStringConst) {
          if (sig->isExplicitlyNamed() && (fC->Type(sig->getPortExpression()) ==
                                           VObjectType::slStringConst)) {
            signame = sig->getFileContent()->SymName(sig->getPortExpression());
          } else if (sig->isExplicitlyNamed() &&
                     (fC->Type(sig->getPortExpression()) ==
                      VObjectType::paPort_expression)) {
            port* dest_port = (*netlist->ports())[portIndex];
            any* exp = m_helper.compileExpression(
                comp, fC, sig->getPortExpression(), m_compileDesign, Reduce::No,
                dest_port, instance, false);
            if (exp->UhdmType() == uhdmoperation) {
              operation* op = (operation*)exp;
              // We don't compute proper typespec
              op->Typespec(nullptr);
            }
            dest_port->Low_conn(exp);
            portIndex++;
            continue;
          } else {
            signame = sig->getName();
          }
        } else {
          portIndex++;
          continue;
        }

        port* dest_port = (*netlist->ports())[portIndex];

        if (sig->getModPort() || sig->getInterfaceDef()) {
          // No rebind
        } else {
          if (any* n = bind_net_(netlist->getParent(), signame)) {
            NodeId typeSpecId = sig->getTypeSpecId();
            if (fC->Type(typeSpecId) == VObjectType::paImplicit_data_type) {
              // interconnect
              if (n->UhdmType() == uhdmlogic_net) {
                logic_net* net = (logic_net*)n;
                net->VpiNetType(vpiNone);
              }
            }
            ref_obj* ref = s.MakeRef_obj();
            ref->VpiName(signame);
            ref->VpiFullName(netlist->getParent()->getFullPathName() + "." +
                             signame);
            fC->populateCoreMembers(sig->getNodeId(), sig->getNodeId(), ref);
            ref->Actual_group(n);
            ref->VpiParent(dest_port);
            dest_port->Low_conn(ref);
          }
        }
      }
      portIndex++;
    }
  }

  return true;
}

UHDM::any* NetlistElaboration::bind_net_(const FileContent* origfC, NodeId id,
                                         ModuleInstance* instance,
                                         ModuleInstance* boundInstance,
                                         std::string_view name) {
  UHDM::any* result = nullptr;
  if (boundInstance) {
    result = bind_net_(boundInstance, name);
  }
  ModuleInstance* itrInst = instance;
  while (result == nullptr) {
    if (itrInst == nullptr) break;
    const FileContent* fC = itrInst->getFileContent();
    NodeId Udp_instantiation = itrInst->getNodeId();
    VObjectType insttype = fC->Type(Udp_instantiation);

    result = bind_net_(itrInst, name);

    if ((insttype != VObjectType::paConditional_generate_construct) &&
        (insttype != VObjectType::paLoop_generate_construct) &&
        (insttype != VObjectType::paGenerate_item) &&
        (insttype != VObjectType::paGenerate_region) &&
        (insttype != VObjectType::paGenerate_module_conditional_statement) &&
        (insttype != VObjectType::paGenerate_interface_conditional_statement) &&
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
    }
    itrInst = itrInst->getParent();
  }
  if (instance && (result == nullptr)) {
    DesignComponent* component = instance->getDefinition();
    if (component) {
      for (const auto& tp : component->getTypeDefMap()) {
        TypeDef* tpd = tp.second;
        typespec* tps = tpd->getTypespec();
        if (tps && tps->UhdmType() == uhdmenum_typespec) {
          enum_typespec* etps = (enum_typespec*)tps;
          for (auto n : *etps->Enum_consts()) {
            if (n->VpiName() == name) {
              return n;
            }
          }
        }
      }
      for (const auto& tp : component->getDataTypeMap()) {
        const DataType* dt = tp.second;
        dt = dt->getActual();
        typespec* tps = dt->getTypespec();
        if (tps && tps->UhdmType() == uhdmenum_typespec) {
          enum_typespec* etps = (enum_typespec*)tps;
          for (auto n : *etps->Enum_consts()) {
            if (n->VpiName() == name) {
              return n;
            }
          }
        }
      }
    }
    m_helper.checkForLoops(true);
    result =
        m_helper.getValue(name, instance->getDefinition(), m_compileDesign,
                          Reduce::Yes, instance, BadPathId, 0, nullptr, true);
    m_helper.checkForLoops(false);
  }
  if ((instance != nullptr) && (result == nullptr)) {
    if (Netlist* netlist = instance->getNetlist()) {
      if (name.find('.') == std::string::npos) {  // Not for hierarchical names
        DesignComponent* component = instance->getDefinition();
        VObjectType implicitNetType =
            component->getDesignElement()
                ? component->getDesignElement()->m_defaultNetType
                : VObjectType::paNetType_Wire;
        if (implicitNetType == VObjectType::slNoType) {
          SymbolTable* symbols =
              m_compileDesign->getCompiler()->getSymbolTable();
          ErrorContainer* errors =
              m_compileDesign->getCompiler()->getErrorContainer();

          Location loc(origfC->getFileId(),
                       id ? origfC->Line(id) : instance->getLineNb(),
                       id ? origfC->Column(id) : instance->getColumnNb(),
                       symbols->registerSymbol(name));
          Error err(ErrorDefinition::ELAB_ILLEGAL_IMPLICIT_NET, loc);
          errors->addError(err);
        }
        // Implicit net
        Serializer& s = m_compileDesign->getSerializer();
        logic_net* net = s.MakeLogic_net();
        net->VpiName(name);
        net->VpiNetType(UhdmWriter::getVpiNetType(implicitNetType));
        origfC->populateCoreMembers(id, id, net);
        result = net;
        Netlist::SymbolTable& symbols = netlist->getSymbolTable();
        std::vector<UHDM::net*>* nets = netlist->nets();
        if (nets == nullptr) {
          nets = s.MakeNetVec();
          netlist->nets(nets);
        }
        nets->push_back(net);
        symbols.emplace(name, result);
      }
    }
  }
  return result;
}

any* NetlistElaboration::bind_net_(ModuleInstance* instance,
                                   std::string_view name) {
  any* result = nullptr;
  Netlist* netlist = instance->getNetlist();
  if (netlist) {
    Netlist::SymbolTable& symbols = netlist->getSymbolTable();
    Netlist::SymbolTable::iterator itr = symbols.find(name);
    if (itr != symbols.end()) {
      return (*itr).second;
    } else {
      std::string_view basename = name;
      std::string_view subname;
      if (basename.find('.') != std::string::npos) {
        subname = basename;
        subname = StringUtils::ltrim_until(subname, '.');
        basename = StringUtils::rtrim_until(basename, '.');
      }
      itr = symbols.find(basename);
      if (itr != symbols.end()) {
        BaseClass* baseclass = (*itr).second;
        port* conn = any_cast<port*>(baseclass);
        ref_obj* ref1 = nullptr;
        const interface_inst* interf = nullptr;
        if (conn) {
          ref1 = any_cast<ref_obj*>((BaseClass*)conn->Low_conn());
        }
        if (ref1) {
          interf = any_cast<interface_inst*>((BaseClass*)ref1->Actual_group());
        }
        if (interf == nullptr) {
          interf = any_cast<interface_inst*>(baseclass);
        }
        if ((interf == nullptr) && ref1) {
          modport* mport = any_cast<modport*>((BaseClass*)ref1->Actual_group());
          if (mport) {
            interf = mport->Interface_inst();
          }
        }
        if (interf) {
          VectorOfnet* nets = interf->Nets();
          if (nets) {
            for (net* p : *nets) {
              if (p->VpiName() == subname) {
                return p;
              }
            }
          }
        } else {
          modport* mport = any_cast<modport*>(baseclass);
          if (mport) {
            VectorOfio_decl* ios = mport->Io_decls();
            if (ios) {
              for (io_decl* decl : *ios) {
                if (decl->VpiName() == subname) {
                  return decl->Expr();
                }
              }
            }
          }
        }
      } else {
        if (netlist->variables()) {
          for (variables* var : *netlist->variables()) {
            if (var->VpiName() == name) {
              return var;
            }
          }
        }
        if (netlist->array_vars()) {
          for (variables* var : *netlist->array_vars()) {
            if (var->VpiName() == name) {
              return var;
            }
          }
        }
        if (netlist->interfaces()) {
          for (interface_inst* var : *netlist->interfaces()) {
            if (var->VpiName() == name) {
              return var;
            }
          }
          for (interface_inst* var : *netlist->interfaces()) {
            std::string_view basename =
                StringUtils::rtrim_until(var->VpiName(), '[');
            if (basename == name) {
              return var;
            }
          }
        }
      }
    }
  }
  return result;
}
}  // namespace SURELOG
