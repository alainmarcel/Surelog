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
 * File:   UhdmWriter.cpp
 * Author: alain
 *
 * Created on January 17, 2020, 9:13 PM
 */

#include "Surelog/DesignCompile/UhdmWriter.h"

#include <uhdm/BaseClass.h>
#include <uhdm/expr.h>
#include <uhdm/uhdm_types.h>

#include <algorithm>
#include <cstdint>
#include <cstring>
#include <filesystem>
#include <iostream>
#include <iterator>
#include <map>
#include <queue>
#include <set>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "Surelog/CommandLine/CommandLineParser.h"
#include "Surelog/Common/Containers.h"
#include "Surelog/Common/FileSystem.h"
#include "Surelog/Common/NodeId.h"
#include "Surelog/Common/SymbolId.h"
#include "Surelog/Design/ClockingBlock.h"
#include "Surelog/Design/DataType.h"
#include "Surelog/Design/DesignElement.h"
#include "Surelog/Design/FileContent.h"
#include "Surelog/Design/ModPort.h"
#include "Surelog/Design/ModuleDefinition.h"
#include "Surelog/Design/ModuleInstance.h"
#include "Surelog/Design/Netlist.h"
#include "Surelog/Design/Parameter.h"
#include "Surelog/Design/Signal.h"
#include "Surelog/Design/ValuedComponentI.h"
#include "Surelog/DesignCompile/CompileDesign.h"
#include "Surelog/DesignCompile/CompileHelper.h"
#include "Surelog/DesignCompile/UhdmChecker.h"
#include "Surelog/ErrorReporting/Error.h"
#include "Surelog/ErrorReporting/ErrorDefinition.h"
#include "Surelog/ErrorReporting/Location.h"
#include "Surelog/Expression/Value.h"
#include "Surelog/Package/Package.h"
#include "Surelog/SourceCompile/Compiler.h"
#include "Surelog/SourceCompile/SymbolTable.h"
#include "Surelog/SourceCompile/VObjectTypes.h"
#include "Surelog/Testbench/ClassDefinition.h"
#include "Surelog/Testbench/Program.h"
#include "Surelog/Testbench/TypeDef.h"
#include "Surelog/Testbench/Variable.h"
#include "Surelog/Utils/StringUtils.h"

// UHDM
#include <uhdm/ElaboratorListener.h>
#include <uhdm/ExprEval.h>
#include <uhdm/Serializer.h>
#include <uhdm/SynthSubset.h>
#include <uhdm/UhdmAdjuster.h>
#include <uhdm/UhdmLint.h>
#include <uhdm/VpiListener.h>
#include <uhdm/clone_tree.h>
#include <uhdm/sv_vpi_user.h>
#include <uhdm/uhdm.h>
#include <uhdm/vpi_uhdm.h>
#include <uhdm/vpi_user.h>
#include <uhdm/vpi_visitor.h>

namespace SURELOG {
namespace fs = std::filesystem;
using namespace UHDM;  // NOLINT (we're using a whole bunch of these)

static typespec* replace(
    const typespec* orig,
    std::map<const UHDM::typespec*, const UHDM::typespec*>& typespecSwapMap) {
  if (orig && (orig->UhdmType() == uhdmunsupported_typespec)) {
    std::map<const typespec*, const typespec*>::const_iterator itr =
        typespecSwapMap.find(orig);
    if (itr != typespecSwapMap.end()) {
      const typespec* tps = (*itr).second;
      return (typespec*)tps;
    }
  }
  return (typespec*)orig;
}

std::string UhdmWriter::builtinGateName(VObjectType type) {
  std::string modName;
  switch (type) {
    case VObjectType::paNInpGate_And:
      modName = "work@and";
      break;
    case VObjectType::paNInpGate_Or:
      modName = "work@or";
      break;
    case VObjectType::paNInpGate_Nand:
      modName = "work@nand";
      break;
    case VObjectType::paNInpGate_Nor:
      modName = "work@nor";
      break;
    case VObjectType::paNInpGate_Xor:
      modName = "work@xor";
      break;
    case VObjectType::paNInpGate_Xnor:
      modName = "work@xnor";
      break;
    case VObjectType::paNOutGate_Buf:
      modName = "work@buf";
      break;
    case VObjectType::paNOutGate_Not:
      modName = "work@not";
      break;
    case VObjectType::paPassEnSwitch_Tranif0:
      modName = "work@tranif0";
      break;
    case VObjectType::paPassEnSwitch_Tranif1:
      modName = "work@tranif1";
      break;
    case VObjectType::paPassEnSwitch_RTranif1:
      modName = "work@rtranif1";
      break;
    case VObjectType::paPassEnSwitch_RTranif0:
      modName = "work@rtranif0";
      break;
    case VObjectType::paPassSwitch_Tran:
      modName = "work@tran";
      break;
    case VObjectType::paPassSwitch_RTran:
      modName = "work@rtran";
      break;
    case VObjectType::paCmosSwitchType_Cmos:
      modName = "work@cmos";
      break;
    case VObjectType::paCmosSwitchType_RCmos:
      modName = "work@rcmos";
      break;
    case VObjectType::paEnableGateType_Bufif0:
      modName = "work@bufif0";
      break;
    case VObjectType::paEnableGateType_Bufif1:
      modName = "work@bufif1";
      break;
    case VObjectType::paEnableGateType_Notif0:
      modName = "work@notif0";
      break;
    case VObjectType::paEnableGateType_Notif1:
      modName = "work@notif1";
      break;
    case VObjectType::paMosSwitchType_NMos:
      modName = "work@nmos";
      break;
    case VObjectType::paMosSwitchType_PMos:
      modName = "work@pmos";
      break;
    case VObjectType::paMosSwitchType_RNMos:
      modName = "work@rnmos";
      break;
    case VObjectType::paMosSwitchType_RPMos:
      modName = "work@rpmos";
      break;
    case VObjectType::paPULLUP:
      modName = "work@pullup";
      break;
    case VObjectType::paPULLDOWN:
      modName = "work@pulldown";
      break;
    default:
      modName = "work@UnsupportedPrimitive";
      break;
  }
  return modName;
}

UhdmWriter::UhdmWriter(CompileDesign* compiler, Design* design)
    : m_compileDesign(compiler), m_design(design), m_uhdmDesign(nullptr) {
  m_helper.seterrorReporting(
      m_compileDesign->getCompiler()->getErrorContainer(),
      m_compileDesign->getCompiler()->getSymbolTable());
}

uint32_t UhdmWriter::getStrengthType(VObjectType type) {
  switch (type) {
    case VObjectType::paSUPPLY0:
      return vpiSupply0;
    case VObjectType::paSUPPLY1:
      return vpiSupply1;
    case VObjectType::paSTRONG0:
      return vpiStrongDrive;
    case VObjectType::paSTRONG1:
      return vpiStrongDrive;
    case VObjectType::paPULL0:
      return vpiPullDrive;
    case VObjectType::paPULL1:
      return vpiPullDrive;
    case VObjectType::paWEAK0:
      return vpiWeakDrive;
    case VObjectType::paWEAK1:
      return vpiWeakDrive;
    case VObjectType::paHIGHZ0:
      return vpiHighZ;
    case VObjectType::paHIGHZ1:
      return vpiHighZ;
    default:
      return 0;
  }
}

uint32_t UhdmWriter::getVpiOpType(VObjectType type) {
  switch (type) {
    case VObjectType::paBinOp_Plus:
      return vpiAddOp;
    case VObjectType::paBinOp_Minus:
      return vpiSubOp;
    case VObjectType::paBinOp_Mult:
      return vpiMultOp;
    case VObjectType::paBinOp_MultMult:
      return vpiPowerOp;
    case VObjectType::paBinOp_Div:
      return vpiDivOp;
    case VObjectType::paBinOp_Great:
      return vpiGtOp;
    case VObjectType::paBinOp_GreatEqual:
      return vpiGeOp;
    case VObjectType::paBinOp_Less:
      return vpiLtOp;
    case VObjectType::paBinOp_Imply:
      return vpiImplyOp;
    case VObjectType::paBinOp_Equivalence:
      return vpiEqOp;
    case VObjectType::paBinOp_LessEqual:
      return vpiLeOp;
    case VObjectType::paBinOp_Equiv:
      return vpiEqOp;
    case VObjectType::paBinOp_Not:
    case VObjectType::paNOT:
      return vpiNeqOp;
    case VObjectType::paBinOp_Percent:
      return vpiModOp;
    case VObjectType::paBinOp_LogicAnd:
      return vpiLogAndOp;
    case VObjectType::paBinOp_LogicOr:
      return vpiLogOrOp;
    case VObjectType::paBinOp_BitwAnd:
      return vpiBitAndOp;
    case VObjectType::paBinOp_BitwOr:
      return vpiBitOrOp;
    case VObjectType::paBinOp_BitwXor:
      return vpiBitXorOp;
    case VObjectType::paBinOp_ReductXnor1:
    case VObjectType::paBinOp_ReductXnor2:
    case VObjectType::paBinModOp_ReductXnor1:
    case VObjectType::paBinModOp_ReductXnor2:
      return vpiBitXNorOp;
    case VObjectType::paBinOp_ReductNand:
      return vpiUnaryNandOp;
    case VObjectType::paBinOp_ReductNor:
      return vpiUnaryNorOp;
    case VObjectType::paUnary_Plus:
      return vpiPlusOp;
    case VObjectType::paUnary_Minus:
      return vpiMinusOp;
    case VObjectType::paUnary_Not:
      return vpiNotOp;
    case VObjectType::paUnary_Tilda:
      return vpiBitNegOp;
    case VObjectType::paUnary_BitwAnd:
      return vpiUnaryAndOp;
    case VObjectType::paUnary_BitwOr:
      return vpiUnaryOrOp;
    case VObjectType::paUnary_BitwXor:
      return vpiUnaryXorOp;
    case VObjectType::paUnary_ReductNand:
      return vpiUnaryNandOp;
    case VObjectType::paUnary_ReductNor:
      return vpiUnaryNorOp;
    case VObjectType::paUnary_ReductXnor1:
    case VObjectType::paUnary_ReductXnor2:
      return vpiUnaryXNorOp;
    case VObjectType::paBinOp_ShiftLeft:
      return vpiLShiftOp;
    case VObjectType::paBinOp_ShiftRight:
      return vpiRShiftOp;
    case VObjectType::paBinOp_ArithShiftLeft:
      return vpiArithLShiftOp;
    case VObjectType::paBinOp_ArithShiftRight:
      return vpiArithRShiftOp;
    case VObjectType::paIncDec_PlusPlus:
      return vpiPostIncOp;
    case VObjectType::paIncDec_MinusMinus:
      return vpiPostDecOp;
    case VObjectType::paConditional_operator:
    case VObjectType::paQMARK:
      return vpiConditionOp;
    case VObjectType::paINSIDE:
    case VObjectType::paOpen_range_list:
      return vpiInsideOp;
    case VObjectType::paBinOp_FourStateLogicEqual:
      return vpiCaseEqOp;
    case VObjectType::paBinOp_FourStateLogicNotEqual:
      return vpiCaseNeqOp;
    case VObjectType::paAssignOp_Assign:
      return vpiAssignmentOp;
    case VObjectType::paAssignOp_Add:
      return vpiAddOp;
    case VObjectType::paAssignOp_Sub:
      return vpiSubOp;
    case VObjectType::paAssignOp_Mult:
      return vpiMultOp;
    case VObjectType::paAssignOp_Div:
      return vpiDivOp;
    case VObjectType::paAssignOp_Modulo:
      return vpiModOp;
    case VObjectType::paAssignOp_BitwAnd:
      return vpiBitAndOp;
    case VObjectType::paAssignOp_BitwOr:
      return vpiBitOrOp;
    case VObjectType::paAssignOp_BitwXor:
      return vpiBitXorOp;
    case VObjectType::paAssignOp_BitwLeftShift:
      return vpiLShiftOp;
    case VObjectType::paAssignOp_BitwRightShift:
      return vpiRShiftOp;
    case VObjectType::paAssignOp_ArithShiftLeft:
      return vpiArithLShiftOp;
    case VObjectType::paAssignOp_ArithShiftRight:
      return vpiArithRShiftOp;
    case VObjectType::paMatches:
      return vpiMatchOp;
    case VObjectType::paBinOp_WildcardEqual:
    case VObjectType::paBinOp_WildEqual:
      return vpiWildEqOp;
    case VObjectType::paBinOp_WildcardNotEqual:
    case VObjectType::paBinOp_WildNotEqual:
      return vpiWildNeqOp;
    case VObjectType::paIFF:
      return vpiIffOp;
    case VObjectType::paOR:
      return vpiLogOrOp;
    case VObjectType::paAND:
      return vpiLogAndOp;
    case VObjectType::paNON_OVERLAP_IMPLY:
      return vpiNonOverlapImplyOp;
    case VObjectType::paOVERLAP_IMPLY:
      return vpiOverlapImplyOp;
    case VObjectType::paOVERLAPPED:
      return vpiOverlapFollowedByOp;
    case VObjectType::paNONOVERLAPPED:
      return vpiNonOverlapFollowedByOp;
    case VObjectType::paUNTIL:
      return vpiUntilOp;
    case VObjectType::paS_UNTIL:
      return vpiUntilOp;
    case VObjectType::paUNTIL_WITH:
      return vpiUntilWithOp;
    case VObjectType::paS_UNTIL_WITH:
      return vpiUntilWithOp;
    case VObjectType::paIMPLIES:
      return vpiImpliesOp;
    case VObjectType::paCycle_delay_range:
      return vpiCycleDelayOp;
    case VObjectType::paConsecutive_repetition:
      return vpiConsecutiveRepeatOp;
    case VObjectType::paNon_consecutive_repetition:
      return vpiRepeatOp;
    case VObjectType::paGoto_repetition:
      return vpiGotoRepeatOp;
    case VObjectType::paTHROUGHOUT:
      return vpiThroughoutOp;
    case VObjectType::paWITHIN:
      return vpiWithinOp;
    case VObjectType::paINTERSECT:
      return vpiIntersectOp;
    case VObjectType::paFIRST_MATCH:
      return vpiFirstMatchOp;
    case VObjectType::paSTRONG:
      return vpiOpStrong;
    case VObjectType::paACCEPT_ON:
      return vpiAcceptOnOp;
    case VObjectType::paSYNC_ACCEPT_ON:
      return vpiSyncAcceptOnOp;
    case VObjectType::paREJECT_ON:
      return vpiRejectOnOp;
    case VObjectType::paSYNC_REJECT_ON:
      return vpiSyncRejectOnOp;
    case VObjectType::paNEXTTIME:
      return vpiNexttimeOp;
    case VObjectType::paS_NEXTTIME:
      return vpiNexttimeOp;
    case VObjectType::paALWAYS:
      return vpiAlwaysOp;
    case VObjectType::paEVENTUALLY:
      return vpiEventuallyOp;
    default:
      return 0;
  }
}

bool isMultidimensional(const UHDM::typespec* ts) {
  bool isMultiDimension = false;
  if (ts) {
    if (ts->UhdmType() == uhdmlogic_typespec) {
      logic_typespec* lts = (logic_typespec*)ts;
      if (lts->Ranges() && lts->Ranges()->size() > 1) isMultiDimension = true;
    } else if (ts->UhdmType() == uhdmarray_typespec) {
      array_typespec* lts = (array_typespec*)ts;
      if (lts->Ranges() && lts->Ranges()->size() > 1) isMultiDimension = true;
    } else if (ts->UhdmType() == uhdmpacked_array_typespec) {
      packed_array_typespec* lts = (packed_array_typespec*)ts;
      if (lts->Ranges() && lts->Ranges()->size() > 1) isMultiDimension = true;
    } else if (ts->UhdmType() == uhdmbit_typespec) {
      bit_typespec* lts = (bit_typespec*)ts;
      if (lts->Ranges() && lts->Ranges()->size() > 1) isMultiDimension = true;
    }
  }
  return isMultiDimension;
}

bool writeElabParameters(Serializer& s, ModuleInstance* instance,
                         UHDM::scope* m, ExprBuilder& exprBuilder) {
  Netlist* netlist = instance->getNetlist();
  DesignComponent* mod = instance->getDefinition();

  std::map<std::string_view, any*> paramSet;
  if (netlist->param_assigns()) {
    VectorOfany* params = m->Parameters();
    if (params == nullptr) params = s.MakeAnyVec();
    m->Parameters(params);
    m->Param_assigns(netlist->param_assigns());
  }

  if (mod) {
    VectorOfany* params = m->Parameters();
    if (params == nullptr) params = s.MakeAnyVec();
    m->Parameters(params);
    VectorOfany* orig_params = mod->getParameters();
    if (orig_params) {
      for (auto orig : *orig_params) {
        const std::string_view name = orig->VpiName();
        bool pushed = false;
        // Specifc handling of type parameters
        if (orig->UhdmType() == uhdmtype_parameter) {
          for (auto p : instance->getTypeParams()) {
            if (p->getName() == orig->VpiName()) {
              any* uparam = p->getUhdmParam();
              if (uparam) {
                uparam->VpiParent(m);
                for (VectorOfany::iterator itr = params->begin();
                     itr != params->end(); itr++) {
                  if ((*itr)->VpiName() == p->getName()) {
                    params->erase(itr);
                    break;
                  }
                }
                params->push_back(uparam);
                pushed = true;
              }
              break;
            }
          }
          if (!pushed) {
            // These point to the sole copy (unelaborated)
            for (VectorOfany::iterator itr = params->begin();
                 itr != params->end(); itr++) {
              if ((*itr)->VpiName() == orig->VpiName()) {
                params->erase(itr);
                break;
              }
            }
            params->push_back(orig);
          }
        } else {
          // Regular param
          ElaboratorContext elaboratorContext(&s, false, true);
          any* pclone = UHDM::clone_tree(orig, &elaboratorContext);
          pclone->VpiParent(m);
          paramSet.emplace(name, pclone);

          /*

            Keep the value of the parameter used during definition. The
          param_assign contains the actual value useful for elaboration

          const typespec* ts = ((parameter*)pclone)->Typespec();
          bool multi = isMultidimensional(ts);
          if (((parameter*)pclone)->Ranges() &&
          ((parameter*)pclone)->Ranges()->size() > 1) multi = true;

          if (instance->getComplexValue(name)) {
          } else {
            Value* val = instance->getValue(name, exprBuilder);
            if (val && val->isValid() && (!multi)) {
              ((parameter*)pclone)->VpiValue(val->uhdmValue());
            }
          }
          */
          params->push_back(pclone);
        }
      }
    }
  }

  if (netlist->param_assigns()) {
    VectorOfany* params = m->Parameters();
    if (params == nullptr) params = s.MakeAnyVec();
    m->Parameters(params);
    for (auto p : *netlist->param_assigns()) {
      bool found = false;
      for (auto pt : *params) {
        if (pt->VpiName() == p->Lhs()->VpiName()) {
          found = true;
          break;
        }
      }
      if (!found) params->push_back(p->Lhs());
    }
  }

  if (netlist->param_assigns()) {
    for (auto ps : *m->Param_assigns()) {
      ps->VpiParent(m);
      const std::string_view name = ps->Lhs()->VpiName();
      auto itr = paramSet.find(name);
      if (itr != paramSet.end()) {
        ps->Lhs((*itr).second);
      }
    }
  }
  return true;
}

uint32_t UhdmWriter::getVpiDirection(VObjectType type) {
  uint32_t direction = vpiInout;
  if (type == VObjectType::paPortDir_Inp ||
      type == VObjectType::paTfPortDir_Inp)
    direction = vpiInput;
  else if (type == VObjectType::paPortDir_Out ||
           type == VObjectType::paTfPortDir_Out)
    direction = vpiOutput;
  else if (type == VObjectType::paPortDir_Inout ||
           type == VObjectType::paTfPortDir_Inout)
    direction = vpiInout;
  else if (type == VObjectType::paTfPortDir_Ref ||
           type == VObjectType::paTfPortDir_ConstRef)
    direction = vpiRef;
  return direction;
}

uint32_t UhdmWriter::getVpiNetType(VObjectType type) {
  uint32_t nettype = 0;
  switch (type) {
    case VObjectType::paNetType_Wire:
      nettype = vpiWire;
      break;
    case VObjectType::paIntVec_TypeReg:
      nettype = vpiReg;
      break;
    case VObjectType::paNetType_Supply0:
      nettype = vpiSupply0;
      break;
    case VObjectType::paNetType_Supply1:
      nettype = vpiSupply1;
      break;
    case VObjectType::paIntVec_TypeLogic:
      nettype = vpiLogicNet;
      break;
    case VObjectType::paNetType_Wand:
      nettype = vpiWand;
      break;
    case VObjectType::paNetType_Wor:
      nettype = vpiWor;
      break;
    case VObjectType::paNetType_Tri:
      nettype = vpiTri;
      break;
    case VObjectType::paNetType_Tri0:
      nettype = vpiTri0;
      break;
    case VObjectType::paNetType_Tri1:
      nettype = vpiTri1;
      break;
    case VObjectType::paNetType_TriReg:
      nettype = vpiTriReg;
      break;
    case VObjectType::paNetType_TriAnd:
      nettype = vpiTriAnd;
      break;
    case VObjectType::paNetType_TriOr:
      nettype = vpiTriOr;
      break;
    case VObjectType::paNetType_Uwire:
      nettype = vpiUwire;
      break;
    case VObjectType::paImplicit_data_type:
    case VObjectType::paSigning_Signed:
    case VObjectType::paPacked_dimension:
    case VObjectType::paSigning_Unsigned:
      nettype = vpiNone;
      break;
    default:
      break;
  }
  return nettype;
}

void UhdmWriter::writePorts(std::vector<Signal*>& orig_ports, BaseClass* parent,
                            VectorOfport* dest_ports, VectorOfnet* dest_nets,
                            Serializer& s, ModPortMap& modPortMap,
                            SignalBaseClassMap& signalBaseMap,
                            SignalMap& signalMap, ModuleInstance* instance,
                            ModuleDefinition* mod) {
  int32_t lastPortDirection = vpiInout;
  for (Signal* orig_port : orig_ports) {
    port* dest_port = s.MakePort();
    signalBaseMap.emplace(orig_port, dest_port);
    signalMap.emplace(orig_port->getName(), orig_port);

    if (orig_port->attributes()) {
      dest_port->Attributes(orig_port->attributes());
      for (auto ats : *orig_port->attributes()) {
        ats->VpiParent(dest_port);
      }
    }

    const FileContent* fC = orig_port->getFileContent();
    if (fC->Type(orig_port->getNodeId()) == VObjectType::slStringConst)
      dest_port->VpiName(orig_port->getName());
    if (orig_port->getDirection() != VObjectType::slNoType)
      lastPortDirection =
          UhdmWriter::getVpiDirection(orig_port->getDirection());
    dest_port->VpiDirection(lastPortDirection);
    orig_port->getFileContent()->populateCoreMembers(
        orig_port->getNodeId(), orig_port->getNodeId(), dest_port);
    dest_port->VpiParent(parent);
    if (ModPort* orig_modport = orig_port->getModPort()) {
      ref_obj* ref = s.MakeRef_obj();
      ref->VpiName(orig_port->getName());
      ref->VpiParent(dest_port);
      dest_port->Low_conn(ref);
      std::map<ModPort*, modport*>::iterator itr =
          modPortMap.find(orig_modport);
      if (itr != modPortMap.end()) {
        ref->Actual_group((*itr).second);
      }
    } else if (ModuleDefinition* orig_interf = orig_port->getInterfaceDef()) {
      ref_obj* ref = s.MakeRef_obj();
      ref->VpiName(orig_port->getName());
      ref->VpiParent(dest_port);
      dest_port->Low_conn(ref);
      const auto& found = m_componentMap.find(orig_interf);
      if (found != m_componentMap.end()) {
        ref->Actual_group(found->second);
      }
    } else if (orig_port->isExplicitlyNamed() &&
               (fC->Type(orig_port->getPortExpression()) ==
                VObjectType::slStringConst)) {
      ref_obj* ref = s.MakeRef_obj();
      ref->VpiName(
          orig_port->getFileContent()->SymName(orig_port->getPortExpression()));
      ref->VpiParent(parent);
      dest_port->Low_conn(ref);
      mod->needLateBinding(ref);
    } else if (orig_port->isExplicitlyNamed() &&
               (fC->Type(orig_port->getPortExpression()) ==
                VObjectType::paPort_expression)) {
      any* exp = m_helper.compileExpression(
          mod, fC, orig_port->getPortExpression(), m_compileDesign, Reduce::No,
          dest_port, instance, false);
      if (exp->UhdmType() == uhdmoperation) {
        operation* op = (operation*)exp;
        // We don't compute proper typespec
        op->Typespec(nullptr);
      }
      dest_port->Low_conn(exp);
    }
    if (NodeId defId = orig_port->getDefaultValue()) {
      any* exp =
          m_helper.compileExpression(mod, fC, defId, m_compileDesign,
                                     Reduce::No, dest_port, instance, false);
      dest_port->High_conn(exp);
    }
    if (orig_port->getTypeSpecId() && mod) {
      if (NodeId unpackedDimensions = orig_port->getUnpackedDimension()) {
        int32_t unpackedSize = 0;
        const FileContent* fC = orig_port->getFileContent();
        if (std::vector<UHDM::range*>* ranges = m_helper.compileRanges(
                mod, fC, unpackedDimensions, m_compileDesign, Reduce::No,
                nullptr, instance, unpackedSize, false)) {
          array_typespec* array_ts = s.MakeArray_typespec();
          array_ts->Ranges(ranges);
          array_ts->VpiParent(dest_port);
          fC->populateCoreMembers(orig_port->getTypeSpecId(), InvalidNodeId,
                                  array_ts);
          if (!ranges->empty()) {
            array_ts->VpiEndLineNo(ranges->back()->VpiEndLineNo());
            array_ts->VpiEndColumnNo(ranges->back()->VpiEndColumnNo());
          }
          for (range* r : *ranges) {
            r->VpiParent(array_ts);
            const expr* rrange = r->Right_expr();
            if (rrange->VpiValue() == "STRING:associative") {
              array_ts->VpiArrayType(vpiAssocArray);
              if (const ref_typespec* rt = rrange->Typespec()) {
                if (const typespec* ag = rt->Actual_typespec()) {
                  ref_typespec* cro = s.MakeRef_typespec();
                  cro->VpiParent(array_ts);
                  cro->Actual_typespec(const_cast<typespec*>(ag));
                  array_ts->Index_typespec(cro);
                }
              }
            } else if (rrange->VpiValue() == "STRING:unsized") {
              array_ts->VpiArrayType(vpiDynamicArray);
            } else if (rrange->VpiValue() == "STRING:$") {
              array_ts->VpiArrayType(vpiQueueArray);
            } else {
              array_ts->VpiArrayType(vpiStaticArray);
            }
          }
          if (dest_port->Typespec() == nullptr) {
            ref_typespec* dest_port_rt = s.MakeRef_typespec();
            dest_port_rt->VpiParent(dest_port);
            dest_port->Typespec(dest_port_rt);
          }
          dest_port->Typespec()->Actual_typespec(array_ts);

          if (typespec* ts = m_helper.compileTypespec(
                  mod, fC, orig_port->getTypeSpecId(), m_compileDesign,
                  Reduce::No, array_ts, nullptr, true)) {
            if (array_ts->Elem_typespec() == nullptr) {
              ref_typespec* array_ts_rt = s.MakeRef_typespec();
              array_ts_rt->VpiParent(array_ts);
              array_ts->Elem_typespec(array_ts_rt);
            }
            array_ts->Elem_typespec()->Actual_typespec(ts);
          }
        }
      } else if (typespec* ts = m_helper.compileTypespec(
                     mod, fC, orig_port->getTypeSpecId(), m_compileDesign,
                     Reduce::No, dest_port, nullptr, true)) {
        if (dest_port->Typespec() == nullptr) {
          ref_typespec* dest_port_rt = s.MakeRef_typespec();
          dest_port_rt->VpiParent(dest_port);
          dest_port->Typespec(dest_port_rt);
        }
        dest_port->Typespec()->Actual_typespec(ts);
      }
    }
    dest_ports->push_back(dest_port);
  }
}

void UhdmWriter::writeDataTypes(const DesignComponent::DataTypeMap& datatypeMap,
                                BaseClass* parent,
                                VectorOftypespec* dest_typespecs, Serializer& s,
                                bool setParent) {
  std::set<uint64_t> ids;
  for (const auto& entry : datatypeMap) {
    const DataType* dtype = entry.second;
    if (dtype->getCategory() == DataType::Category::REF) {
      dtype = dtype->getDefinition();
    }
    if (dtype->getCategory() == DataType::Category::TYPEDEF) {
      if (dtype->getTypespec() == nullptr) dtype = dtype->getDefinition();
    }
    typespec* tps = dtype->getTypespec();
    tps = replace(tps, m_compileDesign->getSwapedObjects());
    if (parent->UhdmType() == uhdmpackage) {
      if (tps && (tps->VpiName().find("::") == std::string::npos)) {
        const std::string newName =
            StrCat(parent->VpiName(), "::", tps->VpiName());
        tps->VpiName(newName);
      }
    }

    if (tps) {
      if (!tps->Instance()) {
        if (parent->UhdmType() != uhdmclass_defn)
          tps->Instance((instance*)parent);
      }
      if (setParent) tps->VpiParent(parent);
      if (ids.find(tps->UhdmId()) == ids.end()) {
        dest_typespecs->push_back(tps);
        ids.insert(tps->UhdmId());
      }
    }
  }
}

void UhdmWriter::writeNets(DesignComponent* mod,
                           std::vector<Signal*>& orig_nets, BaseClass* parent,
                           VectorOfnet* dest_nets, Serializer& s,
                           SignalBaseClassMap& signalBaseMap,
                           SignalMap& signalMap, SignalMap& portMap,
                           ModuleInstance* instance /* = nullptr */) {
  for (auto& orig_net : orig_nets) {
    net* dest_net = nullptr;
    if (instance) {
      for (net* net : *instance->getNetlist()->nets()) {
        UhdmWriter::SignalMap::iterator itr = signalMap.find(net->VpiName());
        if (itr == signalMap.end()) {
          if (net->VpiName() == orig_net->getName()) {
            dest_net = net;
            break;
          }
        }
      }
    } else {
      dest_net = s.MakeLogic_net();
    }
    if (dest_net) {
      const FileContent* fC = orig_net->getFileContent();
      if (fC->Type(orig_net->getNodeId()) == VObjectType::slStringConst) {
        auto portItr = portMap.find(orig_net->getName());
        if (portItr != portMap.end()) {
          Signal* sig = (*portItr).second;
          if (sig) {
            UhdmWriter::SignalBaseClassMap::iterator itr =
                signalBaseMap.find(sig);
            if (itr != signalBaseMap.end()) {
              port* p = (port*)((*itr).second);
              NodeId nodeId = orig_net->getNodeId();
              if (p->Low_conn() == nullptr) {
                ref_obj* ref = s.MakeRef_obj();
                ref->VpiName(p->VpiName());
                ref->Actual_group(dest_net);
                ref->VpiParent(p);
                p->Low_conn(ref);
                fC->populateCoreMembers(nodeId, nodeId, ref);
              } else if (p->Low_conn()->UhdmType() == uhdmref_obj) {
                if (!sig->isExplicitlyNamed()) {
                  ref_obj* ref = (ref_obj*)p->Low_conn();
                  ref->VpiName(p->VpiName());
                  if (ref->VpiLineNo() == 0) {
                    fC->populateCoreMembers(nodeId, nodeId, ref);
                  }
                  if (ref->Actual_group() == nullptr) {
                    ref->Actual_group(dest_net);
                  }
                  ref->VpiParent(p);
                }
              }
            }
          }
        } else if (dest_net->Typespec() == nullptr) {
          // compileTypespec function need to account for range
          // location information if there is any in the typespec.
          if (orig_net->getTypeSpecId()) {
            if (typespec* ts = m_helper.compileTypespec(
                    mod, fC, orig_net->getTypeSpecId(), m_compileDesign,
                    Reduce::No, nullptr, nullptr, true)) {
              ref_typespec* rt = s.MakeRef_typespec();
              rt->VpiParent(dest_net);
              rt->Actual_typespec(ts);
              dest_net->Typespec(rt);
              NodeId dimensions = orig_net->getUnpackedDimension();
              if (!dimensions) dimensions = orig_net->getPackedDimension();
              if (dimensions) {
                fC->populateCoreMembers(InvalidNodeId, dimensions, ts);
              }
            }
          }
        }
        signalBaseMap.emplace(orig_net, dest_net);
        signalMap.emplace(orig_net->getName(), orig_net);
        dest_net->VpiName(orig_net->getName());
        orig_net->getFileContent()->populateCoreMembers(
            orig_net->getNodeId(), orig_net->getNodeId(), dest_net);
        dest_net->VpiNetType(UhdmWriter::getVpiNetType(orig_net->getType()));
        dest_net->VpiParent(parent);
        dest_nets->push_back(dest_net);

        // Handle attributes (similar to writePorts)
        if (orig_net->attributes()) {
          dest_net->Attributes(orig_net->attributes());
          for (auto ats : *orig_net->attributes()) {
            ats->VpiParent(dest_net);
          }
        }
      }
    }
  }
}

void mapLowConns(std::vector<Signal*>& orig_ports, Serializer& s,
                 UhdmWriter::SignalBaseClassMap& signalBaseMap) {
  for (Signal* orig_port : orig_ports) {
    if (Signal* lowconn = orig_port->getLowConn()) {
      UhdmWriter::SignalBaseClassMap::iterator itrlow =
          signalBaseMap.find(lowconn);
      if (itrlow != signalBaseMap.end()) {
        UhdmWriter::SignalBaseClassMap::iterator itrport =
            signalBaseMap.find(orig_port);
        if (itrport != signalBaseMap.end()) {
          ref_obj* ref = s.MakeRef_obj();
          ((port*)itrport->second)->Low_conn(ref);
          ref->VpiParent(itrport->second);
          ref->Actual_group(itrlow->second);

          const FileContent* fC = orig_port->getFileContent();
          fC->populateCoreMembers(orig_port->getNodeId(),
                                  orig_port->getNodeId(), ref);
        }
      }
    }
  }
}

void UhdmWriter::writeClass(ClassDefinition* classDef,
                            VectorOfclass_defn* dest_classes, Serializer& s,
                            BaseClass* parent) {
  if (!classDef->getFileContents().empty() &&
      classDef->getType() == VObjectType::paClass_declaration) {
    const FileContent* fC = classDef->getFileContents()[0];
    class_defn* c = classDef->getUhdmDefinition();
    m_componentMap.emplace(classDef, c);
    c->VpiParent(parent);
    c->VpiEndLabel(classDef->getEndLabel());
    // Typepecs
    VectorOftypespec* typespecs = s.MakeTypespecVec();
    c->Typespecs(typespecs);
    writeDataTypes(classDef->getDataTypeMap(), c, typespecs, s, true);

    // Variables
    // Already bound in TestbenchElaboration

    // Function and tasks
    c->Task_funcs(classDef->getTask_funcs());
    if (c->Task_funcs()) {
      for (auto tf : *c->Task_funcs()) {
        if (tf->VpiParent() == nullptr) tf->VpiParent(c);
      }
    }
    // Parameters
    if (classDef->getParameters()) {
      c->Parameters(classDef->getParameters());
      for (auto ps : *c->Parameters()) {
        ps->VpiParent(c);
      }
    }
    // Extends, fix late binding
    if (const extends* ext = c->Extends()) {
      if (const ref_typespec* ext_rt = ext->Class_typespec()) {
        if (const class_typespec* tps =
                ext_rt->Actual_typespec<UHDM::class_typespec>()) {
          if (tps->Class_defn() == nullptr) {
            const std::string_view tpsName = tps->VpiName();
            if (c->Parameters()) {
              for (auto ps : *c->Parameters()) {
                if (ps->VpiName() == tpsName) {
                  if (ps->UhdmType() == uhdmtype_parameter) {
                    type_parameter* tp = (type_parameter*)ps;
                    if (const UHDM::ref_typespec* tp_rt = tp->Typespec()) {
                      if (const class_typespec* cptp =
                              tp_rt->Actual_typespec<UHDM::class_typespec>()) {
                        ((class_typespec*)tps)
                            ->Class_defn((class_defn*)cptp->Class_defn());
                      }
                    }
                  }
                }
              }
            }
          }
        }
      }
    }

    // Param_assigns
    if (classDef->getParam_assigns()) {
      c->Param_assigns(classDef->getParam_assigns());
      for (auto ps : *c->Param_assigns()) {
        ps->VpiParent(c);
      }
    }
    c->VpiParent(parent);
    dest_classes->push_back(c);
    const std::string_view name = classDef->getName();
    if (c->VpiName().empty()) c->VpiName(name);
    if (c->VpiFullName().empty()) c->VpiFullName(name);
    if (classDef->Attributes() != nullptr) {
      c->Attributes(classDef->Attributes());
      for (auto a : *c->Attributes()) {
        a->VpiParent(c);
      }
    }
    if (fC) {
      // Builtin classes have no file
      const NodeId modId = classDef->getNodeIds()[0];
      const NodeId startId = fC->sl_collect(modId, VObjectType::paCLASS);
      fC->populateCoreMembers(startId, modId, c);
    }
    // Activate when hier_path is better supported
    // lateTypedefBinding(s, classDef, c);
    // lateBinding(s, classDef, c);

    for (auto& nested : classDef->getClassMap()) {
      ClassDefinition* c_nested = nested.second;
      VectorOfclass_defn* dest_classes = s.MakeClass_defnVec();
      writeClass(c_nested, dest_classes, s, c);
    }
  }
}

void UhdmWriter::writeClasses(ClassNameClassDefinitionMultiMap& orig_classes,
                              VectorOfclass_defn* dest_classes, Serializer& s,
                              BaseClass* parent) {
  for (auto& orig_class : orig_classes) {
    ClassDefinition* classDef = orig_class.second;
    writeClass(classDef, dest_classes, s, parent);
  }
}

void UhdmWriter::writeVariables(const DesignComponent::VariableMap& orig_vars,
                                BaseClass* parent, VectorOfvariables* dest_vars,
                                Serializer& s) {
  for (auto& orig_var : orig_vars) {
    Variable* var = orig_var.second;
    const DataType* dtype = var->getDataType();
    const ClassDefinition* classdef =
        datatype_cast<const ClassDefinition*>(dtype);
    if (classdef) {
      class_var* cvar = s.MakeClass_var();
      cvar->VpiName(var->getName());
      var->getFileContent()->populateCoreMembers(var->getNodeId(),
                                                 var->getNodeId(), cvar);
      cvar->VpiParent(parent);
      const auto& found = m_componentMap.find(classdef);
      if (found != m_componentMap.end()) {
        // TODO: Bind Class type,
        // class_var -> class_typespec -> class_defn
      }
      dest_vars->push_back(cvar);
    }
  }
}

class ReInstanceTypespec : public VpiListener {
 public:
  explicit ReInstanceTypespec(package* p) : m_package(p) {}
  ~ReInstanceTypespec() override = default;

  void leaveAny(const any* object, vpiHandle handle) final {
    if (any_cast<const typespec*>(object) != nullptr) {
      if ((object->UhdmType() != uhdmevent_typespec) &&
          (object->UhdmType() != uhdmimport_typespec) &&
          (object->UhdmType() != uhdmtype_parameter)) {
        reInstance(object);
      }
    }
  }

  void leaveFunction(const function* object, vpiHandle handle) final {
    reInstance(object);
  }
  void leaveTask(const task* object, vpiHandle handle) final {
    reInstance(object);
  }
  void reInstance(const any* cobject) {
    if (cobject == nullptr) return;
    any* object = (any*)cobject;
    const instance* inst = nullptr;
    if (typespec* tps = any_cast<typespec*>(object)) {
      inst = tps->Instance();
    } else if (function* tps = any_cast<function*>(object)) {
      inst = tps->Instance();
    } else if (task* tps = any_cast<task*>(object)) {
      inst = tps->Instance();
    }
    if (inst) {
      const std::string_view name = inst->VpiName();
      design* d = (design*)m_package->VpiParent();
      if (d->AllPackages() != nullptr) {
        for (auto pack : *d->AllPackages()) {
          if (pack->VpiName() == name) {
            if (typespec* tps = any_cast<typespec*>(object)) {
              tps->Instance(pack);
              if (const enum_typespec* et =
                      any_cast<const enum_typespec*>(cobject)) {
                reInstance(et->Base_typespec());
              }
            } else if (function* tps = any_cast<function*>(object)) {
              tps->Instance(pack);
            } else if (task* tps = any_cast<task*>(object)) {
              tps->Instance(pack);
            }
            break;
          }
        }
      }
    }
  }

 private:
  package* m_package = nullptr;
};

// Non-elaborated package typespec Instance relation need to point to
// non-elablarated package
void reInstanceTypespec(Serializer& serializer, any* root, package* p) {
  ReInstanceTypespec* listener = new ReInstanceTypespec(p);
  vpiHandle handle = serializer.MakeUhdmHandle(root->UhdmType(), root);
  listener->listenAny(handle);
  vpi_release_handle(handle);
  delete listener;
}

void UhdmWriter::writePackage(Package* pack, package* p, Serializer& s,
                              bool elaborated) {
  p->VpiEndLabel(pack->getEndLabel());
  p->VpiFullName(StrCat(pack->getName(), "::"));
  VectorOfclass_defn* dest_classes = nullptr;

  // Typepecs
  VectorOftypespec* typespecs = s.MakeTypespecVec();
  p->Typespecs(typespecs);
  writeDataTypes(pack->getDataTypeMap(), p, typespecs, s, true);
  writeImportedSymbols(pack, s, typespecs);
  for (auto tp : *typespecs) {
    tp->Instance(p);
  }
  // Classes
  ClassNameClassDefinitionMultiMap& orig_classes = pack->getClassDefinitions();
  dest_classes = s.MakeClass_defnVec();
  writeClasses(orig_classes, dest_classes, s, p);
  p->Class_defns(dest_classes);
  // Parameters
  if (pack->getParameters()) {
    p->Parameters(pack->getParameters());
    for (auto ps : *p->Parameters()) {
      ps->VpiParent(p);
      if (ps->UhdmType() == uhdmparameter) {
        ((parameter*)ps)
            ->VpiFullName(StrCat(pack->getName(), "::", ps->VpiName()));
      } else {
        ((type_parameter*)ps)
            ->VpiFullName(StrCat(pack->getName(), "::", ps->VpiName()));
      }
    }
  }

  // Param_assigns

  if (pack->getParam_assigns()) {
    p->Param_assigns(pack->getParam_assigns());
    for (auto ps : *p->Param_assigns()) {
      ps->VpiParent(p);
      reInstanceTypespec(s, ps, p);
    }
  }

  if (p->Typespecs()) {
    for (auto t : *p->Typespecs()) {
      reInstanceTypespec(s, t, p);
    }
  }

  if (p->Variables()) {
    for (auto v : *p->Variables()) {
      reInstanceTypespec(s, v, p);
    }
  }

  // Function and tasks
  if (pack->getTask_funcs()) {
    p->Task_funcs(s.MakeTask_funcVec());
    for (auto tf : *pack->getTask_funcs()) {
      const std::string_view funcName = tf->VpiName();
      if (funcName.find("::") != std::string::npos) {
        std::vector<std::string_view> res;
        StringUtils::tokenizeMulti(funcName, "::", res);
        const std::string_view className = res[0];
        const std::string_view funcName = res[1];
        bool foundParentClass = false;
        for (auto cl : *dest_classes) {
          if (cl->VpiName() == className) {
            tf->VpiParent(cl);
            tf->Instance(p);
            if (cl->Task_funcs() == nullptr) {
              cl->Task_funcs(s.MakeTask_funcVec());
            }
            cl->Task_funcs()->push_back(tf);
            foundParentClass = true;
            break;
          }
        }
        if (foundParentClass) {
          tf->VpiName(funcName);
          ((task_func*)tf)
              ->VpiFullName(StrCat(pack->getName(), "::", className,
                                   "::", tf->VpiName()));
        } else {
          tf->VpiParent(p);
          tf->Instance(p);
          p->Task_funcs()->push_back(tf);
          ((task_func*)tf)
              ->VpiFullName(StrCat(pack->getName(), "::", tf->VpiName()));
        }
      } else {
        tf->VpiParent(p);
        tf->Instance(p);
        p->Task_funcs()->push_back(tf);
        ((task_func*)tf)
            ->VpiFullName(StrCat(pack->getName(), "::", tf->VpiName()));
      }
    }
  }
  // Variables
  Netlist* netlist = pack->getNetlist();
  if (netlist) {
    p->Variables(netlist->variables());
    if (netlist->variables()) {
      for (auto obj : *netlist->variables()) {
        obj->VpiParent(p);
        ((variables*)obj)
            ->VpiFullName(StrCat(pack->getName(), "::", obj->VpiName()));
      }
    }
  }
  // Nets
  SignalBaseClassMap signalBaseMap;
  SignalMap portMap;
  SignalMap netMap;
  std::vector<Signal*> orig_nets = pack->getSignals();
  VectorOfnet* dest_nets = s.MakeNetVec();
  writeNets(pack, orig_nets, p, dest_nets, s, signalBaseMap, netMap, portMap,
            nullptr);
  p->Nets(dest_nets);
  if (elaborated) {
    lateTypedefBinding(s, pack, p);
  }
  lateBinding(s, pack, p);
}

void UhdmWriter::writeImportedSymbols(DesignComponent* mod, Serializer& s,
                                      VectorOftypespec* typespecs) {
  for (auto item : mod->getImportedSymbols()) {
    bool append = true;
    for (auto tpsiter : *typespecs) {
      if (item->VpiName() == tpsiter->VpiName()) {
        append = false;
        break;
      }
    }
    if (append) {  // Prevents multiple definition
      typespecs->push_back(item);
    }
    constant* c = item->Item();
    if (c) {
      std::string_view packName = item->VpiName();
      std::string_view typeName = c->VpiDecompile();
      Package* pack =
          m_compileDesign->getCompiler()->getDesign()->getPackage(packName);
      if (pack) {
        const auto& itr = m_componentMap.find(pack);
        if (itr != m_componentMap.end()) {
          package* p = (package*)itr->second;
          typespec* tps = nullptr;
          enum_const* cts = nullptr;
          if (p->Typespecs()) {
            for (auto n : *p->Typespecs()) {
              if (n->VpiName() == typeName) {
                tps = n;
                break;
              }
              const std::string pname = StrCat(p->VpiName(), "::", typeName);
              if (n->VpiName() == pname) {
                tps = n;
                break;
              }
              if (n->UhdmType() == uhdmenum_typespec) {
                enum_typespec* tpsiter = any_cast<enum_typespec*>(n);
                if (tpsiter && tpsiter->Enum_consts()) {
                  for (auto c : *tpsiter->Enum_consts()) {
                    if (c->VpiName() == typeName) {
                      cts = c;
                      tps = tpsiter;
                      break;
                    }
                    if (pname == c->VpiName()) {
                      cts = c;
                      tps = tpsiter;
                      break;
                    }
                  }
                }
              }
              if (cts) break;
            }
          }
          if (cts) {
            // Ideally we would want to import only the given symbol,
            // But Synlig does not process that properly, so instead we import
            // the whole enum
            bool append = true;
            for (auto tpsiter : *typespecs) {
              if (tps->VpiName() == tpsiter->VpiName()) {
                append = false;
                break;
              }
            }
            if (append) {  // Prevents multiple definition
              ElaboratorContext elaboratorContext(&s, false, true);
              typespec* item =
                  (typespec*)UHDM::clone_tree(tps, &elaboratorContext);
              typespecs->push_back(item);
            }
          } else if (tps) {
            bool append = true;
            for (auto tpsiter : *typespecs) {
              if (tps->VpiName() == tpsiter->VpiName()) {
                append = false;
                break;
              }
            }
            if (append) {  // Prevents multiple definition
              ElaboratorContext elaboratorContext(&s, false, true);
              typespec* item =
                  (typespec*)UHDM::clone_tree(tps, &elaboratorContext);
              item->VpiName(typeName);
              typespecs->push_back(item);
            }
          }
        }
      }
    }
  }
}

void UhdmWriter::writeModule(ModuleDefinition* mod, module_inst* m,
                             Serializer& s, ModuleMap& moduleMap,
                             ModPortMap& modPortMap, ModuleInstance* instance) {
  SignalBaseClassMap signalBaseMap;
  SignalMap portMap;
  SignalMap netMap;

  m->VpiEndLabel(mod->getEndLabel());

  // Let decls
  if (!mod->getLetStmts().empty()) {
    VectorOflet_decl* decls = s.MakeLet_declVec();
    m->Let_decls(decls);
    for (auto stmt : mod->getLetStmts()) {
      const_cast<let_decl*>(stmt.second->Decl())->VpiParent(m);
      decls->push_back((let_decl*)stmt.second->Decl());
    }
  }
  // Gen stmts
  if (mod->getGenStmts()) {
    m->Gen_stmts(mod->getGenStmts());
    for (auto stmt : *mod->getGenStmts()) {
      stmt->VpiParent(m);
    }
  }
  if (!mod->getPropertyDecls().empty()) {
    VectorOfproperty_decl* decls = s.MakeProperty_declVec();
    m->Property_decls(decls);
    for (auto decl : mod->getPropertyDecls()) {
      decl->VpiParent(m);
      decls->push_back(decl);
    }
  }
  if (!mod->getSequenceDecls().empty()) {
    VectorOfsequence_decl* decls = s.MakeSequence_declVec();
    m->Sequence_decls(decls);
    for (auto decl : mod->getSequenceDecls()) {
      decl->VpiParent(m);
      decls->push_back(decl);
    }
  }

  // Typepecs
  VectorOftypespec* typespecs = s.MakeTypespecVec();
  m->Typespecs(typespecs);
  writeDataTypes(mod->getDataTypeMap(), m, typespecs, s, true);
  writeImportedSymbols(mod, s, typespecs);
  // Ports
  std::vector<Signal*>& orig_ports = mod->getPorts();
  VectorOfport* dest_ports = s.MakePortVec();
  VectorOfnet* dest_nets = s.MakeNetVec();
  writePorts(orig_ports, m, dest_ports, dest_nets, s, modPortMap, signalBaseMap,
             portMap, instance, mod);
  m->Ports(dest_ports);
  // Nets
  std::vector<Signal*> orig_nets = mod->getSignals();
  writeNets(mod, orig_nets, m, dest_nets, s, signalBaseMap, netMap, portMap,
            instance);
  m->Nets(dest_nets);
  mapLowConns(orig_ports, s, signalBaseMap);
  // Classes
  ClassNameClassDefinitionMultiMap& orig_classes = mod->getClassDefinitions();
  VectorOfclass_defn* dest_classes = s.MakeClass_defnVec();
  writeClasses(orig_classes, dest_classes, s, m);
  m->Class_defns(dest_classes);
  // Variables
  // DesignComponent::VariableMap& orig_vars = mod->getVariables();
  // VectorOfvariables* dest_vars = s.MakeVariablesVec();
  // writeVariables(orig_vars, m, dest_vars, s);
  // m->Variables(dest_vars);

  // Cont assigns
  m->Cont_assigns(mod->getContAssigns());
  if (m->Cont_assigns()) {
    for (auto ps : *m->Cont_assigns()) {
      ps->VpiParent(m);
    }
  }

  // Processes
  m->Process(mod->getProcesses());
  if (m->Process()) {
    for (auto ps : *m->Process()) {
      ps->VpiParent(m);
    }
  }
  // Parameters
  if (mod->getParameters()) {
    m->Parameters(mod->getParameters());
    for (auto ps : *m->Parameters()) {
      ps->VpiParent(m);
    }
  }
  // Param_assigns
  if (mod->getParam_assigns()) {
    m->Param_assigns(mod->getParam_assigns());
    for (auto ps : *m->Param_assigns()) {
      ps->VpiParent(m);
    }
  }
  // Function and tasks
  if (auto from = mod->getTask_funcs()) {
    UHDM::VectorOftask_func* target = m->Task_funcs();
    if (target == nullptr) {
      m->Task_funcs(s.MakeTask_funcVec());
      target = m->Task_funcs();
    }
    for (auto tf : *from) {
      target->push_back(tf);
      if (tf->VpiParent() == nullptr) tf->VpiParent(m);
      if (tf->Instance() == nullptr) tf->Instance(m);
    }
  }

  // ClockingBlocks
  for (const auto& ctupple : mod->getClockingBlockMap()) {
    const ClockingBlock& cblock = ctupple.second;
    cblock.getActual()->VpiParent(m);
    switch (cblock.getType()) {
      case ClockingBlock::Type::Default: {
        m->Default_clocking(cblock.getActual());
        break;
      }
      case ClockingBlock::Type::Global: {
        m->Global_clocking(cblock.getActual());
        break;
      }
      case ClockingBlock::Type::Regular: {
        VectorOfclocking_block* cblocks = m->Clocking_blocks();
        if (cblocks == nullptr) {
          m->Clocking_blocks(s.MakeClocking_blockVec());
          cblocks = m->Clocking_blocks();
        }
        cblocks->push_back(cblock.getActual());
        break;
      }
    }
  }

  // Assertions
  if (mod->getAssertions()) {
    m->Assertions(mod->getAssertions());
    for (auto ps : *m->Assertions()) {
      ps->VpiParent(m);
    }
  }
  // Module Instantiation
  if (std::vector<UHDM::ref_module*>* subModules = mod->getRefModules()) {
    m->Ref_modules(subModules);
    for (auto subModArr : *subModules) {
      subModArr->VpiParent(m);
    }
  }
  if (VectorOfmodule_array* subModuleArrays = mod->getModuleArrays()) {
    m->Module_arrays(subModuleArrays);
    for (auto subModArr : *subModuleArrays) {
      subModArr->VpiParent(m);
    }
  }
  if (UHDM::VectorOfprimitive* subModules = mod->getPrimitives()) {
    m->Primitives(subModules);
    for (auto subModArr : *subModules) {
      subModArr->VpiParent(m);
    }
  }
  if (UHDM::VectorOfprimitive_array* subModules = mod->getPrimitiveArrays()) {
    m->Primitive_arrays(subModules);
    for (auto subModArr : *subModules) {
      subModArr->VpiParent(m);
    }
  }
  // Late bind
  if (mod) {
    lateBinding(s, mod, m);
  }
  // Interface instantiation
  const std::vector<Signal*>& signals = mod->getSignals();
  if (!signals.empty()) {
    VectorOfinterface_array* subInterfaceArrays = s.MakeInterface_arrayVec();
    m->Interface_arrays(subInterfaceArrays);
    for (Signal* sig : signals) {
      NodeId unpackedDimension = sig->getUnpackedDimension();
      if (unpackedDimension && sig->getInterfaceDef()) {
        int32_t unpackedSize = 0;
        const FileContent* fC = sig->getFileContent();
        if (std::vector<UHDM::range*>* unpackedDimensions =
                m_helper.compileRanges(mod, fC, unpackedDimension,
                                       m_compileDesign, Reduce::No, nullptr,
                                       instance, unpackedSize, false)) {
          NodeId id = sig->getNodeId();
          const std::string typeName = sig->getInterfaceTypeName();
          interface_array* smarray = s.MakeInterface_array();
          smarray->Ranges(unpackedDimensions);
          for (auto d : *unpackedDimensions) d->VpiParent(smarray);
          if (fC->Type(id) == VObjectType::slStringConst) {
            smarray->VpiName(sig->getName());
          }
          smarray->VpiFullName(typeName);
          smarray->VpiParent(m);
          fC->populateCoreMembers(id, id, smarray);

          NodeId typespecStart = sig->getInterfaceTypeNameId();
          NodeId typespecEnd = typespecStart;
          while (fC->Sibling(typespecEnd)) {
            typespecEnd = fC->Sibling(typespecEnd);
          }
          interface_typespec* tps = s.MakeInterface_typespec();
          if (smarray->Elem_typespec() == nullptr) {
            ref_typespec* tps_rt = s.MakeRef_typespec();
            tps_rt->VpiParent(smarray);
            smarray->Elem_typespec(tps_rt);
          }
          smarray->Elem_typespec()->Actual_typespec(tps);
          tps->VpiName(typeName);
          fC->populateCoreMembers(typespecStart, typespecEnd, tps);

          subInterfaceArrays->push_back(smarray);
        }
      }
    }
  }
  lateBinding(s, mod, m);
}

void UhdmWriter::writeInterface(ModuleDefinition* mod, interface_inst* m,
                                Serializer& s, ModPortMap& modPortMap,
                                ModuleInstance* instance) {
  SignalBaseClassMap signalBaseMap;
  SignalMap portMap;
  SignalMap netMap;

  m->VpiEndLabel(mod->getEndLabel());

  // Let decls
  if (!mod->getLetStmts().empty()) {
    VectorOflet_decl* decls = s.MakeLet_declVec();
    m->Let_decls(decls);
    for (auto stmt : mod->getLetStmts()) {
      decls->push_back((let_decl*)stmt.second->Decl());
    }
  }
  // Gen stmts
  if (mod->getGenStmts()) {
    m->Gen_stmts(mod->getGenStmts());
    for (auto stmt : *mod->getGenStmts()) {
      stmt->VpiParent(m);
    }
  }
  if (!mod->getPropertyDecls().empty()) {
    VectorOfproperty_decl* decls = s.MakeProperty_declVec();
    m->Property_decls(decls);
    for (auto decl : mod->getPropertyDecls()) {
      decl->VpiParent(m);
      decls->push_back(decl);
    }
  }
  if (!mod->getSequenceDecls().empty()) {
    VectorOfsequence_decl* decls = s.MakeSequence_declVec();
    m->Sequence_decls(decls);
    for (auto decl : mod->getSequenceDecls()) {
      decl->VpiParent(m);
      decls->push_back(decl);
    }
  }

  // Typepecs
  VectorOftypespec* typespecs = s.MakeTypespecVec();
  m->Typespecs(typespecs);
  writeDataTypes(mod->getDataTypeMap(), m, typespecs, s, true);
  writeImportedSymbols(mod, s, typespecs);
  // Ports
  std::vector<Signal*>& orig_ports = mod->getPorts();
  VectorOfport* dest_ports = s.MakePortVec();
  VectorOfnet* dest_nets = s.MakeNetVec();
  writePorts(orig_ports, m, dest_ports, dest_nets, s, modPortMap, signalBaseMap,
             portMap, instance);
  m->Ports(dest_ports);
  std::vector<Signal*> orig_nets = mod->getSignals();
  writeNets(mod, orig_nets, m, dest_nets, s, signalBaseMap, netMap, portMap,
            instance);
  m->Nets(dest_nets);
  // Modports
  ModuleDefinition::ModPortSignalMap& orig_modports =
      mod->getModPortSignalMap();
  VectorOfmodport* dest_modports = s.MakeModportVec();
  for (auto& orig_modport : orig_modports) {
    modport* dest_modport = s.MakeModport();
    // dest_modport->Interface(m); // Loop in elaboration!
    dest_modport->VpiParent(m);
    const FileContent* orig_fC = orig_modport.second.getFileContent();
    const NodeId orig_nodeId = orig_modport.second.getNodeId();
    orig_fC->populateCoreMembers(orig_nodeId, orig_nodeId, dest_modport);
    modPortMap.emplace(&orig_modport.second, dest_modport);
    dest_modport->VpiName(orig_modport.first);
    VectorOfio_decl* ios = s.MakeIo_declVec();
    for (auto& sig : orig_modport.second.getPorts()) {
      const FileContent* fC = sig.getFileContent();
      io_decl* io = s.MakeIo_decl();
      io->VpiName(sig.getName());
      NodeId id = sig.getNodeId();
      fC->populateCoreMembers(id, id, io);
      if (NodeId Expression = fC->Sibling(id)) {
        m_helper.checkForLoops(true);
        any* exp =
            m_helper.compileExpression(mod, fC, Expression, m_compileDesign,
                                       Reduce::Yes, io, instance, true);
        m_helper.checkForLoops(false);
        io->Expr(exp);
      }
      uint32_t direction = UhdmWriter::getVpiDirection(sig.getDirection());
      io->VpiDirection(direction);
      io->VpiParent(dest_modport);
      ios->push_back(io);
    }
    dest_modport->Io_decls(ios);
    dest_modports->push_back(dest_modport);
  }
  m->Modports(dest_modports);

  // Cont assigns
  if (mod->getContAssigns()) {
    m->Cont_assigns(mod->getContAssigns());
    for (auto ps : *m->Cont_assigns()) {
      ps->VpiParent(m);
    }
  }

  // Assertions
  if (mod->getAssertions()) {
    m->Assertions(mod->getAssertions());
    for (auto ps : *m->Assertions()) {
      ps->VpiParent(m);
    }
  }

  // Processes
  if (mod->getProcesses()) {
    m->Process(mod->getProcesses());
    for (auto ps : *m->Process()) {
      ps->VpiParent(m);
    }
  }

  // Parameters
  if (mod->getParameters()) {
    m->Parameters(mod->getParameters());
    for (auto ps : *m->Parameters()) {
      ps->VpiParent(m);
    }
  }
  // Param_assigns
  if (mod->getParam_assigns()) {
    m->Param_assigns(mod->getParam_assigns());
    for (auto ps : *m->Param_assigns()) {
      ps->VpiParent(m);
    }
  }

  // Function and tasks
  if (mod->getTask_funcs()) {
    m->Task_funcs(mod->getTask_funcs());
    for (auto tf : *m->Task_funcs()) {
      if (tf->VpiParent() == nullptr) tf->VpiParent(m);
      if (tf->Instance() == nullptr) tf->Instance(m);
    }
  }

  // ClockingBlocks
  for (const auto& ctupple : mod->getClockingBlockMap()) {
    const ClockingBlock& cblock = ctupple.second;
    cblock.getActual()->VpiParent(m);
    switch (cblock.getType()) {
      case ClockingBlock::Type::Default: {
        m->Default_clocking(cblock.getActual());
        break;
      }
      case ClockingBlock::Type::Global: {
        m->Global_clocking(cblock.getActual());
        break;
      }
      case ClockingBlock::Type::Regular: {
        VectorOfclocking_block* cblocks = m->Clocking_blocks();
        if (cblocks == nullptr) {
          m->Clocking_blocks(s.MakeClocking_blockVec());
          cblocks = m->Clocking_blocks();
        }
        cblocks->push_back(cblock.getActual());
        break;
      }
    }
  }
}

void UhdmWriter::writeProgram(Program* mod, program* m, Serializer& s,
                              ModPortMap& modPortMap,
                              ModuleInstance* instance) {
  SignalBaseClassMap signalBaseMap;
  SignalMap portMap;
  SignalMap netMap;

  m->VpiEndLabel(mod->getEndLabel());

  // Typepecs
  VectorOftypespec* typespecs = s.MakeTypespecVec();
  m->Typespecs(typespecs);
  writeDataTypes(mod->getDataTypeMap(), m, typespecs, s, true);
  writeImportedSymbols(mod, s, typespecs);
  // Ports
  std::vector<Signal*>& orig_ports = mod->getPorts();
  VectorOfport* dest_ports = s.MakePortVec();
  VectorOfnet* dest_nets = s.MakeNetVec();
  writePorts(orig_ports, m, dest_ports, dest_nets, s, modPortMap, signalBaseMap,
             portMap, instance);
  m->Ports(dest_ports);
  // Nets
  std::vector<Signal*>& orig_nets = mod->getSignals();
  writeNets(mod, orig_nets, m, dest_nets, s, signalBaseMap, netMap, portMap,
            instance);
  m->Nets(dest_nets);
  mapLowConns(orig_ports, s, signalBaseMap);
  // Parameters
  if (mod->getParameters()) {
    m->Parameters(mod->getParameters());
    for (auto ps : *m->Parameters()) {
      ps->VpiParent(m);
    }
  }

  // Assertions
  if (mod->getAssertions()) {
    m->Assertions(mod->getAssertions());
    for (auto ps : *m->Assertions()) {
      ps->VpiParent(m);
    }
  }

  // Param_assigns
  if (mod->getParam_assigns()) {
    m->Param_assigns(mod->getParam_assigns());
    for (auto ps : *m->Param_assigns()) {
      ps->VpiParent(m);
    }
  }
  // Classes
  ClassNameClassDefinitionMultiMap& orig_classes = mod->getClassDefinitions();
  VectorOfclass_defn* dest_classes = s.MakeClass_defnVec();
  writeClasses(orig_classes, dest_classes, s, m);
  m->Class_defns(dest_classes);
  // Variables
  const DesignComponent::VariableMap& orig_vars = mod->getVariables();
  VectorOfvariables* dest_vars = s.MakeVariablesVec();
  writeVariables(orig_vars, m, dest_vars, s);
  m->Variables(dest_vars);

  // Cont assigns
  m->Cont_assigns(mod->getContAssigns());
  if (m->Cont_assigns()) {
    for (auto ps : *m->Cont_assigns()) {
      ps->VpiParent(m);
    }
  }
  // Processes
  m->Process(mod->getProcesses());
  if (m->Process()) {
    for (auto ps : *m->Process()) {
      ps->VpiParent(m);
    }
  }
  m->Task_funcs(mod->getTask_funcs());
  if (m->Task_funcs()) {
    for (auto tf : *m->Task_funcs()) {
      tf->VpiParent(m);
    }
  }

  // ClockingBlocks
  for (const auto& ctupple : mod->getClockingBlockMap()) {
    const ClockingBlock& cblock = ctupple.second;
    cblock.getActual()->VpiParent(m);
    switch (cblock.getType()) {
      case ClockingBlock::Type::Default: {
        m->Default_clocking(cblock.getActual());
        break;
      }
      case ClockingBlock::Type::Regular: {
        VectorOfclocking_block* cblocks = m->Clocking_blocks();
        if (cblocks == nullptr) {
          m->Clocking_blocks(s.MakeClocking_blockVec());
          cblocks = m->Clocking_blocks();
        }
        cblocks->push_back(cblock.getActual());
        break;
      }
      default:
        break;
    }
  }
}

bool UhdmWriter::writeElabProgram(Serializer& s, ModuleInstance* instance,
                                  program* m, ModPortMap& modPortMap) {
  Netlist* netlist = instance->getNetlist();
  DesignComponent* mod = instance->getDefinition();
  if (mod) {
    // Let decls
    if (!mod->getLetStmts().empty()) {
      VectorOflet_decl* decls = s.MakeLet_declVec();
      m->Let_decls(decls);
      for (auto stmt : mod->getLetStmts()) {
        decls->push_back((let_decl*)stmt.second->Decl());
      }
    }
    if (!mod->getPropertyDecls().empty()) {
      VectorOfproperty_decl* decls = s.MakeProperty_declVec();
      m->Property_decls(decls);
      for (auto decl : mod->getPropertyDecls()) {
        decl->VpiParent(m);
        decls->push_back(decl);
      }
    }
    if (!mod->getSequenceDecls().empty()) {
      VectorOfsequence_decl* decls = s.MakeSequence_declVec();
      m->Sequence_decls(decls);
      for (auto decl : mod->getSequenceDecls()) {
        decl->VpiParent(m);
        decls->push_back(decl);
      }
    }
    // Typepecs
    VectorOftypespec* typespecs = s.MakeTypespecVec();
    m->Typespecs(typespecs);
    writeDataTypes(mod->getDataTypeMap(), m, typespecs, s, false);
    writeImportedSymbols(mod, s, typespecs);
    // Assertions
    if (mod->getAssertions()) {
      m->Assertions(mod->getAssertions());
      for (auto ps : *m->Assertions()) {
        ps->VpiParent(m);
      }
    }
  }
  if (netlist) {
    m->Ports(netlist->ports());
    if (netlist->ports()) {
      typedef std::map<const UHDM::modport*, ModPort*> PortModPortMap;
      PortModPortMap portModPortMap;
      for (auto& entry : netlist->getModPortMap()) {
        portModPortMap.emplace(entry.second.second, entry.second.first);
      }

      for (auto obj : *netlist->ports()) {
        obj->VpiParent(m);

        if (auto lc = obj->Low_conn()) {
          if (const ref_obj* ro = any_cast<const ref_obj*>(lc)) {
            if (const any* ag = ro->Actual_group()) {
              if (ag->UhdmType() == UHDM::uhdmmodport) {
                PortModPortMap::const_iterator it1 =
                    portModPortMap.find((const UHDM::modport*)ag);
                if (it1 != portModPortMap.end()) {
                  ModPortMap::const_iterator it2 = modPortMap.find(it1->second);
                  if (it2 != modPortMap.end()) {
                    const_cast<ref_obj*>(ro)->Actual_group(it2->second);
                  }
                }
              }
            }
          }
        }
      }
    }
    m->Nets(netlist->nets());
    if (netlist->nets()) {
      for (auto obj : *netlist->nets()) {
        obj->VpiParent(m);
      }
    }
    m->Gen_scope_arrays(netlist->gen_scopes());
    m->Variables(netlist->variables());
    if (netlist->variables()) {
      for (auto obj : *netlist->variables()) {
        obj->VpiParent(m);
      }
    }
    m->Array_vars(netlist->array_vars());
    if (netlist->array_vars()) {
      for (auto obj : *netlist->array_vars()) {
        obj->VpiParent(m);
      }
    }
    m->Named_events(netlist->named_events());
    if (netlist->named_events()) {
      for (auto obj : *netlist->named_events()) {
        obj->VpiParent(m);
      }
    }
    m->Array_nets(netlist->array_nets());
    if (netlist->array_nets()) {
      for (auto obj : *netlist->array_nets()) {
        obj->VpiParent(m);
      }
    }

    // Cont assigns
    m->Cont_assigns(mod->getContAssigns());
    if (m->Cont_assigns()) {
      for (auto ps : *m->Cont_assigns()) {
        ps->VpiParent(m);
      }
    }
    // Processes
    m->Process(mod->getProcesses());
    if (m->Process()) {
      for (auto ps : *m->Process()) {
        ps->VpiParent(m);
      }
    }
  }
  if (mod) {
    if (auto from = mod->getTask_funcs()) {
      UHDM::VectorOftask_func* target = m->Task_funcs();
      if (target == nullptr) {
        m->Task_funcs(s.MakeTask_funcVec());
        target = m->Task_funcs();
      }
      for (auto tf : *from) {
        target->push_back(tf);
        if (tf->VpiParent() == nullptr) tf->VpiParent(m);
        if (tf->Instance() == nullptr) tf->Instance(m);
      }
    }
  }

  if (mod) {
    // ClockingBlocks
    ModuleDefinition* def = (ModuleDefinition*)mod;
    for (const auto& ctupple : def->getClockingBlockMap()) {
      const ClockingBlock& cblock = ctupple.second;
      switch (cblock.getType()) {
        case ClockingBlock::Type::Default: {
          ElaboratorContext elaboratorContext(&s, false, true);
          clocking_block* cb = (clocking_block*)UHDM::clone_tree(
              cblock.getActual(), &elaboratorContext);
          cb->VpiParent(m);
          m->Default_clocking(cb);
          break;
        }
        case ClockingBlock::Type::Global: {
          // m->Global_clocking(cblock.getActual());
          break;
        }
        case ClockingBlock::Type::Regular: {
          ElaboratorContext elaboratorContext(&s, false, true);
          clocking_block* cb = (clocking_block*)UHDM::clone_tree(
              cblock.getActual(), &elaboratorContext);
          cb->VpiParent(m);
          VectorOfclocking_block* cblocks = m->Clocking_blocks();
          if (cblocks == nullptr) {
            m->Clocking_blocks(s.MakeClocking_blockVec());
            cblocks = m->Clocking_blocks();
          }
          cblocks->push_back(cb);
          break;
        }
      }
    }
  }

  if (mod) {
    lateTypedefBinding(s, mod, m);
    lateBinding(s, mod, m);
  }

  return true;
}

class DetectUnsizedConstant final : public VpiListener {
 public:
  DetectUnsizedConstant() = default;
  bool unsizedDetected() { return unsized_; }

 private:
  void leaveConstant(const constant* object, vpiHandle handle) final {
    if (object->VpiSize() == -1) unsized_ = true;
  }
  bool unsized_ = false;
};

void UhdmWriter::writeCont_assign(Netlist* netlist, Serializer& s,
                                  DesignComponent* mod, any* m,
                                  std::vector<cont_assign*>* assigns) {
  FileSystem* const fileSystem = FileSystem::getInstance();
  if (netlist->cont_assigns()) {
    for (auto assign : *netlist->cont_assigns()) {
      const expr* lhs = assign->Lhs();
      const expr* rhs = assign->Rhs();
      const expr* delay = assign->Delay();
      const typespec* tps = nullptr;
      if (const ref_typespec* rt = lhs->Typespec()) {
        tps = rt->Actual_typespec();
      }
      bool simplified = false;
      bool cloned = false;
      if (delay && delay->UhdmType() == uhdmref_obj) {
        UHDM::any* var = m_helper.bindParameter(
            mod, netlist->getParent(), delay->VpiName(), m_compileDesign, true);
        ElaboratorContext elaboratorContext(&s, false, true);
        assign = (cont_assign*)UHDM::clone_tree(assign, &elaboratorContext);
        lhs = assign->Lhs();
        rhs = assign->Rhs();
        if (const ref_typespec* rt = lhs->Typespec()) {
          tps = rt->Actual_typespec();
        }
        delay = assign->Delay();
        ref_obj* ref = (ref_obj*)delay;
        ref->Actual_group(var);
        cloned = true;
      }

      if (lhs->UhdmType() == uhdmref_obj) {
        UHDM::any* var =
            m_helper.bindVariable(mod, m, lhs->VpiName(), m_compileDesign);
        if (var) {
          if (rhs->UhdmType() == uhdmoperation) {
            if (cloned == false) {
              ElaboratorContext elaboratorContext(&s, false, true);
              const UHDM::any* pp = assign->VpiParent();
              assign =
                  (cont_assign*)UHDM::clone_tree(assign, &elaboratorContext);
              if (pp != nullptr) assign->VpiParent(const_cast<UHDM::any*>(pp));
              lhs = assign->Lhs();
              rhs = assign->Rhs();
              m_helper.checkForLoops(true);
              bool invalidValue = false;
              any* rhstmp = m_helper.reduceExpr(
                  (expr*)rhs, invalidValue, mod, m_compileDesign,
                  netlist->getParent(),
                  fileSystem->toPathId(
                      rhs->VpiFile(),
                      m_compileDesign->getCompiler()->getSymbolTable()),
                  rhs->VpiLineNo(), assign, true);
              m_helper.checkForLoops(false);
              if (const ref_typespec* rt = lhs->Typespec()) {
                tps = rt->Actual_typespec();
              }
              if (expr* exp = any_cast<expr*>(var)) {
                if (const ref_typespec* rt = exp->Typespec()) {
                  if (const typespec* temp = rt->Actual_typespec()) {
                    tps = temp;
                  }
                }
              }
              if ((invalidValue == false) && rhstmp) {
                if (rhstmp->UhdmType() == uhdmconstant)
                  rhstmp = m_helper.adjustSize(tps, mod, m_compileDesign,
                                               netlist->getParent(),
                                               (constant*)rhstmp, true);
                assign->Rhs((expr*)rhstmp);
              }
              rhs = assign->Rhs();
              delay = assign->Delay();
            }
            ref_obj* ref = (ref_obj*)lhs;
            ref->Actual_group(var);
            cloned = true;
          }

          if (expr* exp = any_cast<expr*>(var)) {
            if (const ref_typespec* rt = exp->Typespec()) {
              if (const typespec* temp = rt->Actual_typespec()) {
                tps = temp;
              }
            }
          }
        }
      }
      if (tps) {
        UHDM::ExprEval eval(true);
        expr* tmp = eval.flattenPatternAssignments(s, tps, (expr*)rhs);
        if (tmp->UhdmType() == uhdmoperation) {
          if (cloned == false) {
            ElaboratorContext elaboratorContext(&s, false, true);
            const UHDM::any* pp = assign->VpiParent();
            assign = (cont_assign*)UHDM::clone_tree(assign, &elaboratorContext);
            if (pp != nullptr) assign->VpiParent(const_cast<UHDM::any*>(pp));
            assign->VpiParent(m);
            lhs = assign->Lhs();
            rhs = assign->Rhs();
            delay = assign->Delay();
            if (const ref_typespec* rt = lhs->Typespec()) {
              tps = rt->Actual_typespec();
            }
            cloned = true;
          }
          ((operation*)rhs)->Operands(((operation*)tmp)->Operands());
          for (auto o : *((operation*)tmp)->Operands()) {
            o->VpiParent(const_cast<expr*>(rhs));
          }
          operation* op = (operation*)rhs;
          int32_t opType = op->VpiOpType();
          if (opType == vpiAssignmentPatternOp || opType == vpiConditionOp) {
            if (m_helper.substituteAssignedValue(rhs, m_compileDesign)) {
              rhs = m_helper.expandPatternAssignment(tps, (UHDM::expr*)rhs, mod,
                                                     m_compileDesign,
                                                     netlist->getParent());
            }
          }
          rhs = (UHDM::expr*)m_helper.defaultPatternAssignment(
              tps, (UHDM::expr*)rhs, mod, m_compileDesign,
              netlist->getParent());

          assign->Rhs((UHDM::expr*)rhs);
          m_helper.reorderAssignmentPattern(mod, lhs, (UHDM::expr*)rhs,
                                            m_compileDesign,
                                            netlist->getParent(), 0);
          simplified = true;
        }
      } else if (rhs->UhdmType() == uhdmoperation) {
        operation* op = (operation*)rhs;
        if (const ref_typespec* ro1 = op->Typespec()) {
          if (const typespec* tps = ro1->Actual_typespec()) {
            UHDM::ExprEval eval(true);
            expr* tmp = eval.flattenPatternAssignments(s, tps, (expr*)rhs);
            if (tmp->UhdmType() == uhdmoperation) {
              if (cloned == false) {
                ElaboratorContext elaboratorContext(&s, false, true);
                assign =
                    (cont_assign*)UHDM::clone_tree(assign, &elaboratorContext);
                assign->VpiParent(m);
                lhs = assign->Lhs();
                rhs = assign->Rhs();
                delay = assign->Delay();
                if (const ref_typespec* ro2 = lhs->Typespec()) {
                  tps = ro2->Actual_typespec();
                }
                cloned = true;
              }
              ((operation*)rhs)->Operands(((operation*)tmp)->Operands());
              simplified = true;
            }
          }
        }
      }
      if (simplified == false) {
        bool invalidValue = false;
        if ((rhs->UhdmType() == uhdmsys_func_call) &&
            ((expr*)rhs)->Typespec() == nullptr) {
          if (((expr*)rhs)->Typespec() == nullptr) {
            ref_typespec* crt = s.MakeRef_typespec();
            crt->VpiParent((expr*)rhs);
            ((expr*)rhs)->Typespec(crt);
          }
          ((expr*)rhs)->Typespec()->Actual_typespec(const_cast<typespec*>(tps));
        }
        m_helper.checkForLoops(true);
        any* res = m_helper.reduceExpr(
            (expr*)rhs, invalidValue, mod, m_compileDesign,
            netlist->getParent(),
            fileSystem->toPathId(
                rhs->VpiFile(),
                m_compileDesign->getCompiler()->getSymbolTable()),
            rhs->VpiLineNo(), assign, true);
        m_helper.checkForLoops(false);
        if (invalidValue == false) {
          if (res && (res->UhdmType() == uhdmconstant)) {
            if (cloned == false) {
              ElaboratorContext elaboratorContext(&s, false, true);
              assign =
                  (cont_assign*)UHDM::clone_tree(assign, &elaboratorContext);
              assign->VpiParent(m);
              lhs = assign->Lhs();
              cloned = true;
              res = m_helper.adjustSize(tps, mod, m_compileDesign,
                                        netlist->getParent(), (constant*)res,
                                        true);
              res->VpiParent(assign);
            }
            assign->Rhs((constant*)res);
          }
        }
      }
      if (simplified == false && cloned == false) {
        DetectUnsizedConstant detector;
        vpiHandle h_rhs = NewVpiHandle(rhs);
        detector.listenAny(h_rhs);
        vpi_free_object(h_rhs);
        if (detector.unsizedDetected()) {
          ElaboratorContext elaboratorContext(&s, false, true);
          assign = (cont_assign*)UHDM::clone_tree(assign, &elaboratorContext);
          assign->VpiParent(m);
          cloned = true;
        }
      }
      if (tps != nullptr) const_cast<typespec*>(tps)->VpiParent(nullptr);
      if (cloned || (assign->VpiParent() == nullptr)) assign->VpiParent(m);
      assigns->push_back(assign);
    }
  }
}

bool UhdmWriter::writeElabGenScope(Serializer& s, ModuleInstance* instance,
                                   gen_scope* m, ExprBuilder& exprBuilder) {
  FileSystem* const fileSystem = FileSystem::getInstance();
  Netlist* netlist = instance->getNetlist();
  ModuleDefinition* mod =
      valuedcomponenti_cast<ModuleDefinition*>(instance->getDefinition());
  if (mod) {
    // Let decls
    if (!mod->getLetStmts().empty()) {
      VectorOflet_decl* decls = s.MakeLet_declVec();
      m->Let_decls(decls);
      for (auto stmt : mod->getLetStmts()) {
        decls->push_back((let_decl*)stmt.second->Decl());
      }
    }
    if (!mod->getPropertyDecls().empty()) {
      VectorOfproperty_decl* decls = s.MakeProperty_declVec();
      m->Property_decls(decls);
      for (auto decl : mod->getPropertyDecls()) {
        decl->VpiParent(m);
        decls->push_back(decl);
      }
    }
    if (!mod->getSequenceDecls().empty()) {
      VectorOfsequence_decl* decls = s.MakeSequence_declVec();
      m->Sequence_decls(decls);
      for (auto decl : mod->getSequenceDecls()) {
        decl->VpiParent(m);
        decls->push_back(decl);
      }
    }
    // Typepecs
    VectorOftypespec* typespecs = s.MakeTypespecVec();
    m->Typespecs(typespecs);
    writeDataTypes(mod->getDataTypeMap(), m, typespecs, s, true);
    writeImportedSymbols(mod, s, typespecs);
    // System elab tasks
    m->Elab_tasks((std::vector<UHDM::tf_call*>*)&mod->getElabSysCalls());
    if (m->Elab_tasks()) {
      for (auto et : *m->Elab_tasks()) {
        et->VpiParent(m);
      }
    }
    // Assertions
    if (mod->getAssertions()) {
      m->Assertions(mod->getAssertions());
      for (auto ps : *m->Assertions()) {
        ps->VpiParent(m);
      }
    }
  }
  if (netlist) {
    m->Nets(netlist->nets());
    if (netlist->nets()) {
      for (auto obj : *netlist->nets()) {
        obj->VpiParent(m);
      }
    }

    if (netlist->cont_assigns()) {
      std::vector<cont_assign*>* assigns = m->Cont_assigns();
      if (assigns == nullptr) {
        m->Cont_assigns(s.MakeCont_assignVec());
        assigns = m->Cont_assigns();
      }
      writeCont_assign(netlist, s, mod, m, assigns);
      for (auto obj : *assigns) {
        obj->VpiParent(m);
      }
    }

    // Processes
    m->Process(netlist->process_stmts());
    if (m->Process()) {
      for (auto ps : *m->Process()) {
        ps->VpiParent(m);
      }
    }

    std::vector<gen_scope_array*>* gen_scope_arrays = netlist->gen_scopes();
    if (gen_scope_arrays) {
      writeElabParameters(s, instance, m, exprBuilder);

      // Loop indexes
      for (auto& param : instance->getMappedValues()) {
        const std::string_view name = param.first;
        Value* val = param.second.first;
        VectorOfany* params = nullptr;
        params = m->Parameters();
        if (params == nullptr) {
          params = s.MakeAnyVec();
        }
        m->Parameters(params);
        bool found = false;
        for (auto p : *params) {
          if (p->VpiName() == name) {
            found = true;
            break;
          }
        }
        if (!found) {
          parameter* p = s.MakeParameter();
          p->VpiName(name);
          if (val && val->isValid()) p->VpiValue(val->uhdmValue());
          p->VpiFile(fileSystem->toPath(instance->getFileId()));
          p->VpiLineNo(param.second.second);
          p->VpiParent(m);
          p->VpiLocalParam(true);
          int_typespec* ts = s.MakeInt_typespec();
          ref_typespec* rt = s.MakeRef_typespec();
          rt->VpiParent(p);
          p->Typespec(rt);
          rt->Actual_typespec(ts);
          params->push_back(p);
        }
      }
    }

    m->Variables(netlist->variables());
    if (netlist->variables()) {
      for (auto obj : *netlist->variables()) {
        obj->VpiParent(m);
      }
    }
    m->Array_vars(netlist->array_vars());
    if (netlist->array_vars()) {
      for (auto obj : *netlist->array_vars()) {
        obj->VpiParent(m);
      }
    }
    m->Named_events(netlist->named_events());
    if (netlist->named_events()) {
      for (auto obj : *netlist->named_events()) {
        obj->VpiParent(m);
      }
    }
    m->Array_nets(netlist->array_nets());
    if (netlist->array_nets()) {
      for (auto obj : *netlist->array_nets()) {
        obj->VpiParent(m);
      }
    }
  }

  DesignComponent* def = instance->getDefinition();
  if (def->getTask_funcs()) {
    // Function and tasks
    UHDM::VectorOftask_func* target = m->Task_funcs();
    if (target == nullptr) {
      m->Task_funcs(s.MakeTask_funcVec());
      target = m->Task_funcs();
    }
    for (auto tf : *def->getTask_funcs()) {
      target->push_back(tf);
      if (tf->VpiParent() == nullptr) tf->VpiParent(m);
    }
  }

  // ClockingBlocks
  for (const auto& ctupple : mod->getClockingBlockMap()) {
    const ClockingBlock& cblock = ctupple.second;
    switch (cblock.getType()) {
      case ClockingBlock::Type::Default: {
        // No default clocking
        // m->Default_clocking(cblock.getActual());
        break;
      }
      case ClockingBlock::Type::Regular: {
        ElaboratorContext elaboratorContext(&s, false, true);
        clocking_block* cb = (clocking_block*)UHDM::clone_tree(
            cblock.getActual(), &elaboratorContext);
        cb->VpiParent(m);
        VectorOfclocking_block* cblocks = m->Clocking_blocks();
        if (cblocks == nullptr) {
          m->Clocking_blocks(s.MakeClocking_blockVec());
          cblocks = m->Clocking_blocks();
        }
        cblocks->push_back(cb);
        break;
      }
      default:
        break;
    }
  }

  return true;
}

UHDM::any* UhdmWriter::swapForSpecifiedVar(UHDM::Serializer& s,
                                           DesignComponent* mod, any* tmp,
                                           VectorOfvariables* lvariables,
                                           variables* lvariable,
                                           std::string_view name,
                                           const any* var, const any* parent) {
  FileSystem* const fileSystem = FileSystem::getInstance();
  if (tmp->VpiName() == name) {
    if (var->UhdmType() == uhdmref_var) {
      ref_var* ref = (ref_var*)var;
      const typespec* tp = nullptr;
      if (ref_typespec* rt = ref->Typespec()) tp = rt->Actual_typespec();
      if (tp && tp->UhdmType() == uhdmunsupported_typespec) {
        const typespec* indexTypespec = nullptr;
        if (lvariables) {
          for (auto var : *lvariables) {
            if (var->UhdmType() == uhdmhier_path) {
              PathId parentFileId = fileSystem->toPathId(
                  parent->VpiFile(),
                  m_compileDesign->getCompiler()->getSymbolTable());
              bool invalidValue = false;
              indexTypespec = (typespec*)m_helper.decodeHierPath(
                  (hier_path*)var, invalidValue, mod, m_compileDesign,
                  Reduce::Yes, nullptr, parentFileId, parent->VpiLineNo(),
                  (any*)parent, true /*mute for now*/, true);
            }
          }
        } else if (const variables* var = lvariable) {
          if (var->UhdmType() == uhdmhier_path) {
            PathId parentFileId = fileSystem->toPathId(
                parent->VpiFile(),
                m_compileDesign->getCompiler()->getSymbolTable());
            bool invalidValue = false;
            indexTypespec = (typespec*)m_helper.decodeHierPath(
                (hier_path*)var, invalidValue, mod, m_compileDesign,
                Reduce::Yes, nullptr, parentFileId, parent->VpiLineNo(),
                (any*)parent, true /*mute for now*/, true);
          } else if (var->UhdmType() == uhdmref_var) {
            bool invalidValue = false;
            hier_path* path = s.MakeHier_path();
            VectorOfany* elems = s.MakeAnyVec();
            path->Path_elems(elems);
            ref_obj* ref = s.MakeRef_obj();
            elems->push_back(ref);
            ref->VpiName(var->VpiName());
            path->VpiFullName(var->VpiName());
            PathId parentFileId = fileSystem->toPathId(
                parent->VpiFile(),
                m_compileDesign->getCompiler()->getSymbolTable());
            indexTypespec = (typespec*)m_helper.decodeHierPath(
                path, invalidValue, mod, m_compileDesign, Reduce::Yes, nullptr,
                parentFileId, parent->VpiLineNo(), (any*)parent,
                true /*mute for now*/, true);
          }
        }
        variables* swapVar = nullptr;
        if (indexTypespec) {
          swapVar = m_helper.getSimpleVarFromTypespec((typespec*)indexTypespec,
                                                      nullptr, m_compileDesign);
        } else {
          int_var* ivar = s.MakeInt_var();
          ref_typespec* rt = s.MakeRef_typespec();
          rt->Actual_typespec(s.MakeInt_typespec());
          rt->VpiParent(ivar);
          ivar->Typespec(rt);
          swapVar = ivar;
        }
        if (swapVar) {
          swapVar->VpiName(ref->VpiName());
          swapVar->VpiParent(const_cast<any*>(ref->VpiParent()));
          swapVar->VpiFile(ref->VpiFile());
          swapVar->VpiLineNo(ref->VpiLineNo());
          swapVar->VpiColumnNo(ref->VpiColumnNo());
          swapVar->VpiEndLineNo(ref->VpiEndLineNo());
          swapVar->VpiEndColumnNo(ref->VpiEndColumnNo());
          tmp = swapVar;
        }
      }
    }
  }
  return tmp;
}

void UhdmWriter::lateTypedefBinding(UHDM::Serializer& s, DesignComponent* mod,
                                    scope* m) {
  for (UHDM::any* var : mod->getLateTypedefBinding()) {
    const typespec* orig = nullptr;
    if (expr* ex = any_cast<expr*>(var)) {
      if (ref_typespec* rt = ex->Typespec()) {
        orig = rt->Actual_typespec();
      }
    } else if (typespec_member* ex = any_cast<typespec_member*>(var)) {
      if (ref_typespec* rt = ex->Typespec()) {
        orig = rt->Actual_typespec();
      }
    } else if (parameter* ex = any_cast<parameter*>(var)) {
      if (ref_typespec* rt = ex->Typespec()) {
        orig = rt->Actual_typespec();
      }
    } else if (type_parameter* ex = any_cast<type_parameter*>(var)) {
      if (ref_typespec* rt = ex->Typespec()) {
        orig = rt->Actual_typespec();
      }
    } else if (io_decl* ex = any_cast<io_decl*>(var)) {
      if (ref_typespec* rt = ex->Typespec()) {
        orig = rt->Actual_typespec();
      }
    }
    if (orig && (orig->UhdmType() == uhdmunsupported_typespec)) {
      unsupported_typespec* unsup = (unsupported_typespec*)orig;
      std::string_view name = StringUtils::trim(orig->VpiName());
      const typespec* tps = nullptr;
      bool found = false;

      if (name.find("::") != std::string::npos) {
        std::vector<std::string_view> res;
        StringUtils::tokenizeMulti(name, "::", res);
        if (res.size() > 1) {
          const std::string_view packName = res[0];
          const std::string_view typeName = res[1];
          Package* pack =
              m_compileDesign->getCompiler()->getDesign()->getPackage(packName);
          if (pack) {
            const auto& itr = m_componentMap.find(pack);
            if (itr != m_componentMap.end()) {
              package* p = (package*)itr->second;
              if (p->Typespecs()) {
                for (auto n : *p->Typespecs()) {
                  if (n->VpiName() == typeName) {
                    found = true;
                    tps = n;
                    break;
                  }
                  const std::string pname =
                      StrCat(p->VpiName(), "::", typeName);
                  if (n->VpiName() == pname) {
                    found = true;
                    tps = n;
                    break;
                  }
                }
              }
            }
          }
        }
      }

      const any* parent = var->VpiParent();
      while (parent) {
        if (parent->UhdmType() == uhdmfunction) {
          function* func = (function*)parent;
          if (parent->VpiName() == name) {
            if (const any* ret = func->Return()) {
              variables* var = (variables*)ret;
              found = true;
              if (const ref_typespec* rt = var->Typespec()) {
                tps = rt->Actual_typespec();
              }
            }
            break;
          }
          if (auto decls = func->Io_decls()) {
            for (auto decl : *decls) {
              if (decl->VpiName() == name) {
                if (decl->UhdmType() == uhdmref_var) continue;
                if (decl->UhdmType() == uhdmref_obj) continue;
                found = true;
                if (const ref_typespec* rt = decl->Typespec()) {
                  tps = rt->Actual_typespec();
                }
                break;
              }
            }
          }
          if (auto vars = func->Variables()) {
            for (auto decl : *vars) {
              if (decl->VpiName() == name) {
                if (decl->UhdmType() == uhdmref_var) continue;
                if (decl->UhdmType() == uhdmref_obj) continue;
                found = true;
                if (const ref_typespec* rt = decl->Typespec()) {
                  tps = rt->Actual_typespec();
                }
                break;
              }
            }
          }
          if (auto params = func->Parameters()) {
            for (auto decl : *params) {
              if (decl->VpiName() == name) {
                found = true;
                if (decl->UhdmType() == uhdmparameter) {
                  if (const ref_typespec* rt = ((parameter*)decl)->Typespec()) {
                    tps = rt->Actual_typespec();
                  }
                } else {
                  if (const ref_typespec* rt =
                          ((type_parameter*)decl)->Typespec()) {
                    tps = rt->Actual_typespec();
                  }
                }
                break;
              }
            }
          }
          if (const UHDM::instance* inst = func->Instance()) {
            if (inst->UhdmType() == uhdmpackage) {
              package* pack = (package*)inst;
              if (pack->Variables()) {
                for (auto n : *pack->Variables()) {
                  if (n->VpiName() == name) {
                    if (n->UhdmType() == uhdmref_var) continue;
                    if (n->UhdmType() == uhdmref_obj) continue;
                    found = true;
                    if (ref_typespec* rt = n->Typespec()) {
                      tps = rt->Actual_typespec();
                    }
                    break;
                  }
                  if (m) {
                    const std::string pname = StrCat(m->VpiName(), "::", name);
                    if (n->VpiName() == pname) {
                      if (n->UhdmType() == uhdmref_var) continue;
                      if (n->UhdmType() == uhdmref_obj) continue;
                      found = true;
                      if (ref_typespec* rt = n->Typespec()) {
                        tps = rt->Actual_typespec();
                      }
                      break;
                    }
                  }
                }
              }
            }
          }
          if (found) break;
        } else if (parent->UhdmType() == uhdmtask) {
          task* ta = (task*)parent;
          if (auto decls = ta->Io_decls()) {
            for (auto decl : *decls) {
              if (decl->VpiName() == name) {
                if (decl->UhdmType() == uhdmref_var) continue;
                if (decl->UhdmType() == uhdmref_obj) continue;
                found = true;
                if (ref_typespec* rt = decl->Typespec()) {
                  tps = rt->Actual_typespec();
                }
                break;
              }
            }
          }
          if (auto vars = ta->Variables()) {
            for (auto decl : *vars) {
              if (decl->VpiName() == name) {
                if (decl->UhdmType() == uhdmref_var) continue;
                if (decl->UhdmType() == uhdmref_obj) continue;
                found = true;
                if (ref_typespec* rt = decl->Typespec()) {
                  tps = rt->Actual_typespec();
                }
                break;
              }
            }
          }
          if (const UHDM::instance* inst = ta->Instance()) {
            if (inst->UhdmType() == uhdmpackage) {
              package* pack = (package*)inst;
              if (pack->Variables()) {
                for (auto n : *pack->Variables()) {
                  if (n->VpiName() == name) {
                    if (n->UhdmType() == uhdmref_var) continue;
                    if (n->UhdmType() == uhdmref_obj) continue;
                    found = true;
                    if (ref_typespec* rt = n->Typespec()) {
                      tps = rt->Actual_typespec();
                    }
                    break;
                  }
                  if (m) {
                    const std::string pname = StrCat(m->VpiName(), "::", name);
                    if (n->VpiName() == pname) {
                      if (n->UhdmType() == uhdmref_var) continue;
                      if (n->UhdmType() == uhdmref_obj) continue;
                      found = true;
                      if (ref_typespec* rt = n->Typespec()) {
                        tps = rt->Actual_typespec();
                      }
                      break;
                    }
                  }
                }
              }
            }
          }
          if (found) break;
        } else if (parent->UhdmType() == uhdmfor_stmt) {
          for_stmt* f = (for_stmt*)parent;
          VectorOfany* inits = f->VpiForInitStmts();
          if (inits) {
            for (auto init : *inits) {
              if (init->UhdmType() == uhdmassignment) {
                assignment* as = (assignment*)init;
                const expr* lhs = as->Lhs();
                if (lhs && lhs->VpiName() == name) {
                  if (lhs->UhdmType() == uhdmref_var) continue;
                  if (lhs->UhdmType() == uhdmref_obj) continue;
                  found = true;
                  if (const ref_typespec* rt = lhs->Typespec()) {
                    tps = rt->Actual_typespec();
                  }
                  break;
                }
              }
            }
          }
        } else if (parent->UhdmType() == uhdmforeach_stmt) {
          foreach_stmt* f = (foreach_stmt*)parent;
          VectorOfany* vars = f->VpiLoopVars();
          if (vars) {
            for (auto& vart : *vars) {
              if (vart->VpiName() == name) {
                if (vart->UhdmType() == uhdmref_var) continue;
                if (vart->UhdmType() == uhdmref_obj) continue;
                found = true;
                if (ref_typespec* rt = ((variables*)vart)->Typespec()) {
                  tps = rt->Actual_typespec();
                }
                if (any* p = var->VpiParent()) {
                  if (p->UhdmType() == uhdmforeach_stmt) {
                    foreach_stmt* fc = (foreach_stmt*)p;
                    VectorOfany* varsc = fc->VpiLoopVars();
                    for (auto& vartc : *varsc) {
                      if (vartc->VpiName() == name) {
                        vartc = vart;
                        break;
                      }
                    }
                  }
                }
                break;
              }
            }
          }
        } else if (parent->UhdmType() == uhdmmodule_inst) {
          module_inst* m = (module_inst*)parent;
          if (auto vars = m->Variables()) {
            for (auto decl : *vars) {
              if (decl->VpiName() == name) {
                if (decl->UhdmType() == uhdmref_var) continue;
                if (decl->UhdmType() == uhdmref_obj) continue;
                found = true;
                if (ref_typespec* rt = decl->Typespec()) {
                  tps = rt->Actual_typespec();
                }
                break;
              }
            }
          }
          if (found) break;
          if (auto params = m->Parameters()) {
            for (auto decl : *params) {
              if (decl->VpiName() == name) {
                if (decl->UhdmType() == uhdmparameter) {
                  if (ref_typespec* rt = ((parameter*)decl)->Typespec()) {
                    tps = rt->Actual_typespec();
                  }
                  found = true;
                } else {
                  if (ref_typespec* rt = ((type_parameter*)decl)->Typespec()) {
                    tps = rt->Actual_typespec();
                  }
                  found = true;
                }
                break;
              }
            }
          }
          if (found) break;
          if (m) {
            VectorOfport* ports = m->Ports();
            if (ports) {
              for (auto port : *ports) {
                if (port->VpiName() == name) {
                  if (ref_typespec* tmp = port->Typespec()) {
                    found = true;
                    tps = tmp->Actual_typespec();
                    break;
                  }
                }
              }
            }
            if (found) break;
            VectorOfnet* nets = m->Nets();
            if (nets) {
              for (auto net : *nets) {
                if (net->VpiName() == name) {
                  if (ref_typespec* tmp = net->Typespec()) {
                    found = true;
                    tps = tmp->Actual_typespec();
                    break;
                  }
                }
              }
            }
            if (found) break;
          }
        } else if (parent->UhdmType() == uhdmbegin) {
          begin* b = (begin*)parent;
          if (auto vars = b->Variables()) {
            for (auto decl : *vars) {
              if (decl->VpiName() == name) {
                if (decl->UhdmType() == uhdmref_var) continue;
                if (decl->UhdmType() == uhdmref_obj) continue;
                found = true;
                if (ref_typespec* rt = decl->Typespec()) {
                  tps = rt->Actual_typespec();
                }
                break;
              }
            }
          }
          if (found) break;
          if (auto params = b->Parameters()) {
            for (auto decl : *params) {
              if (decl->VpiName() == name) {
                if (decl->UhdmType() == uhdmparameter) {
                  if (ref_typespec* rt = ((parameter*)decl)->Typespec()) {
                    tps = rt->Actual_typespec();
                  }
                } else {
                  if (ref_typespec* rt = ((type_parameter*)decl)->Typespec()) {
                    tps = rt->Actual_typespec();
                  }
                }
                break;
              }
            }
          }
          if (found) break;
          VectorOfany* stmts = b->Stmts();
          if (stmts) {
            for (auto init : *stmts) {
              if (init->UhdmType() == uhdmassignment) {
                assignment* as = (assignment*)init;
                const expr* lhs = as->Lhs();
                if (lhs && lhs->VpiName() == name) {
                  if (lhs->UhdmType() == uhdmref_var) continue;
                  if (lhs->UhdmType() == uhdmref_obj) continue;
                  found = true;
                  if (const ref_typespec* rt = lhs->Typespec()) {
                    tps = rt->Actual_typespec();
                  }
                  break;
                }
              }
            }
          }
        } else if (parent->UhdmType() == uhdmnamed_begin) {
          named_begin* b = (named_begin*)parent;
          if (auto vars = b->Variables()) {
            for (auto decl : *vars) {
              if (decl->VpiName() == name) {
                if (decl->UhdmType() == uhdmref_var) continue;
                if (decl->UhdmType() == uhdmref_obj) continue;
                found = true;
                if (const ref_typespec* rt = decl->Typespec()) {
                  tps = rt->Actual_typespec();
                }
                break;
              }
            }
          }
          if (found) break;
          if (auto params = b->Parameters()) {
            for (auto decl : *params) {
              if (decl->VpiName() == name) {
                if (decl->UhdmType() == uhdmparameter) {
                  if (const ref_typespec* rt = ((parameter*)decl)->Typespec()) {
                    tps = rt->Actual_typespec();
                  }
                } else {
                  if (const ref_typespec* rt =
                          ((type_parameter*)decl)->Typespec()) {
                    tps = rt->Actual_typespec();
                  }
                }
                break;
              }
            }
          }
          if (found) break;
          VectorOfany* stmts = b->Stmts();
          if (stmts) {
            for (auto init : *stmts) {
              if (init->UhdmType() == uhdmassignment) {
                assignment* as = (assignment*)init;
                const expr* lhs = as->Lhs();
                if (lhs && lhs->VpiName() == name) {
                  if (lhs->UhdmType() == uhdmref_var) continue;
                  if (lhs->UhdmType() == uhdmref_obj) continue;
                  found = true;
                  if (const ref_typespec* rt = lhs->Typespec()) {
                    tps = rt->Actual_typespec();
                  }
                  break;
                }
              }
            }
          }
        } else if (parent->UhdmType() == uhdmfork_stmt) {
          fork_stmt* b = (fork_stmt*)parent;
          if (auto vars = b->Variables()) {
            for (auto decl : *vars) {
              if (decl->VpiName() == name) {
                if (decl->UhdmType() == uhdmref_var) continue;
                if (decl->UhdmType() == uhdmref_obj) continue;
                found = true;
                if (const ref_typespec* rt = decl->Typespec()) {
                  tps = rt->Actual_typespec();
                }
                break;
              }
            }
          }
          if (found) break;
          if (auto params = b->Parameters()) {
            for (auto decl : *params) {
              if (decl->VpiName() == name) {
                found = true;
                if (decl->UhdmType() == uhdmparameter) {
                  if (const ref_typespec* rt = ((parameter*)decl)->Typespec()) {
                    tps = rt->Actual_typespec();
                  }
                } else {
                  if (const ref_typespec* rt =
                          ((type_parameter*)decl)->Typespec()) {
                    tps = rt->Actual_typespec();
                  }
                }
                break;
              }
            }
          }
          if (found) break;
          VectorOfany* stmts = b->Stmts();
          if (stmts) {
            for (auto init : *stmts) {
              if (init->UhdmType() == uhdmassignment) {
                assignment* as = (assignment*)init;
                const expr* lhs = as->Lhs();
                if (lhs && lhs->VpiName() == name) {
                  if (lhs->UhdmType() == uhdmref_var) continue;
                  if (lhs->UhdmType() == uhdmref_obj) continue;
                  found = true;
                  if (const ref_typespec* rt = lhs->Typespec()) {
                    tps = rt->Actual_typespec();
                  }
                  break;
                }
              }
            }
          }
        } else if (parent->UhdmType() == uhdmnamed_fork) {
          named_fork* b = (named_fork*)parent;
          if (auto vars = b->Variables()) {
            for (auto decl : *vars) {
              if (decl->VpiName() == name) {
                if (decl->UhdmType() == uhdmref_var) continue;
                if (decl->UhdmType() == uhdmref_obj) continue;
                found = true;
                if (const ref_typespec* rt = decl->Typespec()) {
                  tps = rt->Actual_typespec();
                }
                break;
              }
            }
          }
          if (found) break;
          if (auto params = b->Parameters()) {
            for (auto decl : *params) {
              if (decl->VpiName() == name) {
                found = true;
                if (decl->UhdmType() == uhdmparameter) {
                  if (const ref_typespec* rt = ((parameter*)decl)->Typespec()) {
                    tps = rt->Actual_typespec();
                  }
                } else {
                  if (const ref_typespec* rt =
                          ((type_parameter*)decl)->Typespec()) {
                    tps = rt->Actual_typespec();
                  }
                }
                break;
              }
            }
          }
          if (found) break;
          VectorOfany* stmts = b->Stmts();
          if (stmts) {
            for (auto init : *stmts) {
              if (init->UhdmType() == uhdmassignment) {
                assignment* as = (assignment*)init;
                const expr* lhs = as->Lhs();
                if (!lhs) continue;
                if (lhs->UhdmType() == uhdmref_var) continue;
                if (lhs->UhdmType() == uhdmref_obj) continue;
                if (lhs->VpiName() == name) {
                  found = true;
                  if (const ref_typespec* rt = lhs->Typespec()) {
                    tps = rt->Actual_typespec();
                  }
                  break;
                }
              }
            }
          }
        }
        if (found) {
          if (tps) {
            tps = replace(tps, m_compileDesign->getSwapedObjects());
          }

          if (unsup->Ranges()) {
            ref_typespec* tpsRef = s.MakeRef_typespec();
            tpsRef->Actual_typespec(const_cast<UHDM::typespec*>(tps));
            if (unsup->VpiPacked()) {
              packed_array_typespec* ptps = s.MakePacked_array_typespec();
              tpsRef->VpiParent(ptps);
              ptps->Elem_typespec(tpsRef);
              ptps->Ranges(unsup->Ranges());
              tps = ptps;
            } else {
              array_typespec* ptps = s.MakeArray_typespec();
              tpsRef->VpiParent(ptps);
              ptps->Elem_typespec(tpsRef);
              ptps->Ranges(unsup->Ranges());
              tps = ptps;
            }
            if (unsup->Ranges()) {
              for (auto r : *unsup->Ranges()) {
                r->VpiParent(const_cast<typespec*>(tps));
              }
            }
          }
          break;
        }
        parent = parent->VpiParent();
      }

      if (found == false) {
        if (const any* parent = var->VpiParent()) {
          // Foreach-loop, implicit loop var declaration fixup
          if (parent->UhdmType() == uhdmforeach_stmt) {
            foreach_stmt* for_stmt = (foreach_stmt*)parent;
            if (VectorOfany* loopvars = for_stmt->VpiLoopVars()) {
              for (any*& tmp : *loopvars) {
                tmp = swapForSpecifiedVar(s, mod, tmp, for_stmt->Variables(),
                                          for_stmt->Variable(), name, var,
                                          parent);
              }
            }
          } else if (parent->UhdmType() == uhdmassignment) {
            parent = var->VpiParent()->VpiParent();
            // gen_for loop, implicit loop var declaration fixup
            if (parent->UhdmType() == uhdmgen_for) {
              gen_for* for_stmt = (gen_for*)parent;
              if (for_stmt->VpiForInitStmts()) {
                any* stmt = for_stmt->VpiForInitStmts()->at(0);
                if (stmt->UhdmType() == uhdmassignment) {
                  assignment* st = (assignment*)stmt;
                  st->Lhs((expr*)swapForSpecifiedVar(
                      s, mod, st->Lhs(), nullptr, nullptr, name, var, parent));
                }
              }
            }
          }
        }
      }

      if ((name.empty()) && (found == false)) {
        // Port .op({\op[1] ,\op[0] })
        if (operation* op = any_cast<operation*>(var)) {
          const typespec* baseTypespec = nullptr;
          uint64_t size = 0;
          for (any* oper : *op->Operands()) {
            if (oper->UhdmType() == uhdmref_obj) {
              ref_obj* ref = (ref_obj*)oper;
              if (const expr* ex = ref->Actual_group<expr>()) {
                if (const UHDM::ref_typespec* rt = ex->Typespec()) {
                  if (const typespec* tps = rt->Actual_typespec()) {
                    baseTypespec = tps;
                    break;
                  }
                }
              }
            }
            size++;
          }
          if (baseTypespec) {
            array_typespec* arr = s.MakeArray_typespec();
            tps = arr;
            found = true;
            ref_typespec* baseRef = s.MakeRef_typespec();
            baseRef->VpiParent(arr);
            baseRef->Actual_typespec(const_cast<typespec*>(baseTypespec));
            arr->Elem_typespec(baseRef);
            VectorOfrange* ranges = s.MakeRangeVec();
            range* ra = s.MakeRange();
            ranges->push_back(ra);
            constant* l = s.MakeConstant();
            l->VpiValue("UINT:" + std::to_string(size - 1));
            ra->Left_expr(l);
            constant* r = s.MakeConstant();
            r->VpiValue("UINT:0");
            ra->Right_expr(r);
            arr->Ranges(ranges);
          }
        }
      }
      if (found == true) {
        if (tps == nullptr) {
          if (expr* ex = any_cast<expr*>(var)) {
            ex->Typespec(nullptr);
          } else if (typespec_member* ex = any_cast<typespec_member*>(var)) {
            ex->Typespec(nullptr);
          } else if (parameter* ex = any_cast<parameter*>(var)) {
            ex->Typespec(nullptr);
          } else if (type_parameter* ex = any_cast<type_parameter*>(var)) {
            ex->Typespec(nullptr);
          } else if (io_decl* ex = any_cast<io_decl*>(var)) {
            ex->Typespec(nullptr);
          }
        } else {
          if (expr* ex = any_cast<expr*>(var)) {
            if (ex->Typespec() == nullptr) {
              ref_typespec* rt = s.MakeRef_typespec();
              ex->Typespec(rt);
              rt->VpiParent(ex);
            }
            ex->Typespec()->Actual_typespec(const_cast<UHDM::typespec*>(tps));
          } else if (typespec_member* ex = any_cast<typespec_member*>(var)) {
            if (ex->Typespec() == nullptr) {
              ref_typespec* rt = s.MakeRef_typespec();
              ex->Typespec(rt);
              rt->VpiParent(ex);
            }
            ex->Typespec()->Actual_typespec(const_cast<UHDM::typespec*>(tps));
          } else if (parameter* ex = any_cast<parameter*>(var)) {
            if (ex->Typespec() == nullptr) {
              ref_typespec* rt = s.MakeRef_typespec();
              ex->Typespec(rt);
              rt->VpiParent(ex);
            }
            ex->Typespec()->Actual_typespec(const_cast<UHDM::typespec*>(tps));
          } else if (type_parameter* ex = any_cast<type_parameter*>(var)) {
            if (ex->Typespec() == nullptr) {
              ref_typespec* rt = s.MakeRef_typespec();
              ex->Typespec(rt);
              rt->VpiParent(ex);
            }
            ex->Typespec()->Actual_typespec(const_cast<UHDM::typespec*>(tps));
          } else if (io_decl* ex = any_cast<io_decl*>(var)) {
            if (ex->Typespec() == nullptr) {
              ref_typespec* rt = s.MakeRef_typespec();
              ex->Typespec(rt);
              rt->VpiParent(ex);
            }
            ex->Typespec()->Actual_typespec(const_cast<UHDM::typespec*>(tps));
          }
        }
      }
    }
  }
  for (const auto& itr : mod->getLateResolutionFunction()) {
    std::string_view funcName = itr.first;
    std::pair<task_func*, DesignComponent*> ret =
        m_helper.getTaskFunc(funcName, mod, m_compileDesign, nullptr, nullptr);
    task_func* tf = ret.first;
    function* resolution_func = any_cast<function*>(tf);
    typespec* ts = itr.second;
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
      } else if (ts->UhdmType() == uhdmarray_typespec) {
        array_typespec* btps = (array_typespec*)ts;
        btps->Resolution_func(resolution_func);
      } else if (ts->UhdmType() == uhdmpacked_array_typespec) {
        packed_array_typespec* btps = (packed_array_typespec*)ts;
        btps->Resolution_func(resolution_func);
      }
    }
  }
}

void UhdmWriter::lateBinding(Serializer& s, DesignComponent* mod, scope* m) {
  FileSystem* const fileSystem = FileSystem::getInstance();
  for (UHDM::ref_obj* ref : mod->getLateBinding()) {
    if (ref->Actual_group()) continue;
    std::string_view name = ref->VpiName();
    name = StringUtils::trim(name);
    if (name.find("::") != std::string::npos) {
      std::vector<std::string_view> res;
      StringUtils::tokenizeMulti(name, "::", res);
      if (res.size() > 1) {
        const std::string_view packName = res[0];
        const std::string_view typeName = res[1];
        Package* pack =
            m_compileDesign->getCompiler()->getDesign()->getPackage(packName);
        if (pack) {
          const auto& itr = m_componentMap.find(pack);
          if (itr != m_componentMap.end()) {
            package* p = (package*)itr->second;
            if (p->Parameters()) {
              for (auto n : *p->Parameters()) {
                if (n->VpiName() == typeName) {
                  if (n->UhdmType() == uhdmref_var) continue;
                  if (n->UhdmType() == uhdmref_obj) continue;
                  ref->Actual_group(n);
                  break;
                }
                if (m) {
                  const std::string pname =
                      StrCat(m->VpiName(), "::", typeName);
                  if (n->VpiName() == pname) {
                    if (n->UhdmType() == uhdmref_var) continue;
                    if (n->UhdmType() == uhdmref_obj) continue;
                    ref->Actual_group(n);
                    break;
                  }
                }
              }
            }
            if (p->Variables()) {
              for (auto n : *p->Variables()) {
                if (n->VpiName() == typeName) {
                  if (n->UhdmType() == uhdmref_var) continue;
                  if (n->UhdmType() == uhdmref_obj) continue;
                  ref->Actual_group(n);
                  break;
                }
                if (m) {
                  const std::string pname =
                      StrCat(m->VpiName(), "::", typeName);
                  if (n->VpiName() == pname) {
                    if (n->UhdmType() == uhdmref_var) continue;
                    if (n->UhdmType() == uhdmref_obj) continue;
                    ref->Actual_group(n);
                    break;
                  }
                }
              }
            }
          }
        }
      }

      continue;
    }

    const any* parent = ref->VpiParent();
    while (parent) {
      if (parent->UhdmType() == uhdmdesign) {
        design* d = (design*)parent;
        if (auto params = d->Parameters()) {
          for (auto decl : *params) {
            if (decl->VpiName() == name) {
              ref->Actual_group(decl);
              break;
            }
          }
        }
      } else if (parent->UhdmType() == uhdmfunction) {
        function* func = (function*)parent;
        if (parent->VpiName() == name) {
          if (const any* ret = func->Return()) {
            ElaboratorContext elaboratorContext(&s, false, true);
            variables* var =
                (variables*)UHDM::clone_tree(ret, &elaboratorContext);
            var->VpiName(name);
            var->VpiParent(ref);
            ref->Actual_group(var);
          }
          break;
        }
        if (auto decls = func->Io_decls()) {
          for (auto decl : *decls) {
            if (decl->VpiName() == name) {
              if (decl->UhdmType() == uhdmref_var) continue;
              if (decl->UhdmType() == uhdmref_obj) continue;
              ref->Actual_group(decl);
              break;
            }
          }
        }
        if (auto vars = func->Variables()) {
          for (auto decl : *vars) {
            if (decl->VpiName() == name) {
              if (decl->UhdmType() == uhdmref_var) continue;
              if (decl->UhdmType() == uhdmref_obj) continue;
              ref->Actual_group(decl);
              break;
            }
          }
        }
        if (auto params = func->Parameters()) {
          for (auto decl : *params) {
            if (decl->VpiName() == name) {
              ref->Actual_group(decl);
              break;
            }
          }
        }
        if (const UHDM::instance* inst = func->Instance()) {
          if (inst->UhdmType() == uhdmpackage) {
            package* pack = (package*)inst;
            if (pack->Variables()) {
              for (auto n : *pack->Variables()) {
                if (n->VpiName() == name) {
                  if (n->UhdmType() == uhdmref_var) continue;
                  if (n->UhdmType() == uhdmref_obj) continue;
                  ref->Actual_group(n);
                  break;
                }
                if (m) {
                  const std::string pname = StrCat(m->VpiName(), "::", name);
                  if (n->VpiName() == pname) {
                    if (n->UhdmType() == uhdmref_var) continue;
                    if (n->UhdmType() == uhdmref_obj) continue;
                    ref->Actual_group(n);
                    break;
                  }
                }
              }
            }
          }
        }
        if (ref->Actual_group()) break;
      } else if (parent->UhdmType() == uhdmtask) {
        task* ta = (task*)parent;
        if (auto decls = ta->Io_decls()) {
          for (auto decl : *decls) {
            if (decl->VpiName() == name) {
              if (decl->UhdmType() == uhdmref_var) continue;
              if (decl->UhdmType() == uhdmref_obj) continue;
              ref->Actual_group(decl);
              break;
            }
          }
        }
        if (auto vars = ta->Variables()) {
          for (auto decl : *vars) {
            if (decl->VpiName() == name) {
              if (decl->UhdmType() == uhdmref_var) continue;
              if (decl->UhdmType() == uhdmref_obj) continue;
              ref->Actual_group(decl);
              break;
            }
          }
        }
        if (const UHDM::instance* inst = ta->Instance()) {
          if (inst->UhdmType() == uhdmpackage) {
            package* pack = (package*)inst;
            if (pack->Variables()) {
              for (auto n : *pack->Variables()) {
                if (n->VpiName() == name) {
                  if (n->UhdmType() == uhdmref_var) continue;
                  if (n->UhdmType() == uhdmref_obj) continue;
                  ref->Actual_group(n);
                  break;
                }
                if (m) {
                  const std::string pname = StrCat(m->VpiName(), "::", name);
                  if (n->VpiName() == pname) {
                    if (n->UhdmType() == uhdmref_var) continue;
                    if (n->UhdmType() == uhdmref_obj) continue;
                    ref->Actual_group(n);
                    break;
                  }
                }
              }
            }
            if (m->Typespecs()) {
              for (auto n : *m->Typespecs()) {
                if (n->UhdmType() == uhdmenum_typespec) {
                  enum_typespec* tps = any_cast<enum_typespec*>(n);
                  if (tps && tps->Enum_consts()) {
                    for (auto c : *tps->Enum_consts()) {
                      if (c->VpiName() == name) {
                        ref->Actual_group(c);
                        break;
                      }
                      if (std::string(std::string(m->VpiName()) +
                                      std::string("::") + std::string(name)) ==
                          c->VpiName()) {
                        ref->Actual_group(c);
                        break;
                      }
                    }
                  }
                }
              }
            }
          }
        }
        if (ref->Actual_group()) break;
      } else if (parent->UhdmType() == uhdmfor_stmt) {
        for_stmt* f = (for_stmt*)parent;
        VectorOfany* inits = f->VpiForInitStmts();
        if (inits) {
          for (auto init : *inits) {
            if (init->UhdmType() == uhdmassignment) {
              assignment* as = (assignment*)init;
              const expr* lhs = as->Lhs();
              if (lhs && lhs->VpiName() == name) {
                if (lhs->UhdmType() == uhdmref_var) continue;
                if (lhs->UhdmType() == uhdmref_obj) continue;
                ref->Actual_group((expr*)lhs);
                break;
              }
            }
          }
        }
      } else if (parent->UhdmType() == uhdmforeach_stmt) {
        foreach_stmt* f = (foreach_stmt*)parent;
        VectorOfany* vars = f->VpiLoopVars();
        if (vars) {
          for (auto var : *vars) {
            if (var->VpiName() == name) {
              if (var->UhdmType() == uhdmref_var) continue;
              if (var->UhdmType() == uhdmref_obj) continue;
              ref->Actual_group((expr*)var);
              break;
            }
          }
        }
      } else if (parent->UhdmType() == uhdmgen_for) {
        gen_for* for_stmt = (gen_for*)parent;
        if (VectorOfany* inits = for_stmt->VpiForInitStmts()) {
          for (auto init : *inits) {
            if (init->UhdmType() == uhdmassignment) {
              assignment* as = (assignment*)init;
              const expr* lhs = as->Lhs();
              if (lhs && lhs->VpiName() == name) {
                if (lhs->UhdmType() == uhdmref_var) continue;
                if (lhs->UhdmType() == uhdmref_obj) continue;
                ref->Actual_group((expr*)lhs);
                break;
              }
            }
          }
        }
      } else if (parent->UhdmType() == uhdmbegin) {
        begin* b = (begin*)parent;
        if (auto vars = b->Variables()) {
          for (auto decl : *vars) {
            if (decl->VpiName() == name) {
              if (decl->UhdmType() == uhdmref_var) continue;
              if (decl->UhdmType() == uhdmref_obj) continue;
              ref->Actual_group(decl);
              break;
            }
          }
        }
        if (ref->Actual_group()) break;
        if (auto params = b->Parameters()) {
          for (auto decl : *params) {
            if (decl->VpiName() == name) {
              ref->Actual_group(decl);
              break;
            }
          }
        }
        if (ref->Actual_group()) break;
        VectorOfany* stmts = b->Stmts();
        if (stmts) {
          for (auto init : *stmts) {
            if (init->UhdmType() == uhdmassignment) {
              assignment* as = (assignment*)init;
              const expr* lhs = as->Lhs();
              if (lhs && lhs->VpiName() == name) {
                if (lhs->UhdmType() == uhdmref_var) continue;
                if (lhs->UhdmType() == uhdmref_obj) continue;
                ref->Actual_group((expr*)lhs);
                break;
              }
            } else if (init->UhdmType() == uhdmassign_stmt) {
              assign_stmt* as = (assign_stmt*)init;
              const expr* lhs = as->Lhs();
              if (lhs->VpiName() == name) {
                if (lhs->UhdmType() == uhdmref_var) continue;
                if (lhs->UhdmType() == uhdmref_obj) continue;
                ref->Actual_group((expr*)lhs);
                break;
              }
            }
          }
        }
      } else if (parent->UhdmType() == uhdmnamed_begin) {
        named_begin* b = (named_begin*)parent;
        if (auto vars = b->Variables()) {
          for (auto decl : *vars) {
            if (decl->VpiName() == name) {
              if (decl->UhdmType() == uhdmref_var) continue;
              if (decl->UhdmType() == uhdmref_obj) continue;
              ref->Actual_group(decl);
              break;
            }
          }
        }
        if (ref->Actual_group()) break;
        if (auto params = b->Parameters()) {
          for (auto decl : *params) {
            if (decl->VpiName() == name) {
              ref->Actual_group(decl);
              break;
            }
          }
        }
        if (ref->Actual_group()) break;
        VectorOfany* stmts = b->Stmts();
        if (stmts) {
          for (auto init : *stmts) {
            if (init->UhdmType() == uhdmassign_stmt) {
              assign_stmt* as = (assign_stmt*)init;
              const expr* lhs = as->Lhs();
              if (lhs->VpiName() == name) {
                if (lhs->UhdmType() == uhdmref_var) continue;
                if (lhs->UhdmType() == uhdmref_obj) continue;
                ref->Actual_group((expr*)lhs);
                break;
              }
            } else if (init->UhdmType() == uhdmassignment) {
              assignment* as = (assignment*)init;
              const expr* lhs = as->Lhs();
              if (lhs->VpiName() == name) {
                if (lhs->UhdmType() == uhdmref_var) continue;
                if (lhs->UhdmType() == uhdmref_obj) continue;
                ref->Actual_group((expr*)lhs);
                break;
              }
            }
          }
        }
      } else if (parent->UhdmType() == uhdmfork_stmt) {
        fork_stmt* b = (fork_stmt*)parent;
        if (auto vars = b->Variables()) {
          for (auto decl : *vars) {
            if (decl->VpiName() == name) {
              if (decl->UhdmType() == uhdmref_var) continue;
              if (decl->UhdmType() == uhdmref_obj) continue;
              ref->Actual_group(decl);
              break;
            }
          }
        }
        if (ref->Actual_group()) break;
        if (auto params = b->Parameters()) {
          for (auto decl : *params) {
            if (decl->VpiName() == name) {
              ref->Actual_group(decl);
              break;
            }
          }
        }
        if (ref->Actual_group()) break;
        VectorOfany* stmts = b->Stmts();
        if (stmts) {
          for (auto init : *stmts) {
            if (init->UhdmType() == uhdmassign_stmt) {
              assign_stmt* as = (assign_stmt*)init;
              const expr* lhs = as->Lhs();
              if (lhs->VpiName() == name) {
                if (lhs->UhdmType() == uhdmref_var) continue;
                if (lhs->UhdmType() == uhdmref_obj) continue;
                ref->Actual_group((expr*)lhs);
                break;
              }
            } else if (init->UhdmType() == uhdmassignment) {
              assignment* as = (assignment*)init;
              const expr* lhs = as->Lhs();
              if (lhs->VpiName() == name) {
                if (lhs->UhdmType() == uhdmref_var) continue;
                if (lhs->UhdmType() == uhdmref_obj) continue;
                ref->Actual_group((expr*)lhs);
                break;
              }
            }
          }
        }
      } else if (parent->UhdmType() == uhdmnamed_fork) {
        named_fork* b = (named_fork*)parent;
        if (auto vars = b->Variables()) {
          for (auto decl : *vars) {
            if (decl->VpiName() == name) {
              if (decl->UhdmType() == uhdmref_var) continue;
              if (decl->UhdmType() == uhdmref_obj) continue;
              ref->Actual_group(decl);
              break;
            }
          }
        }
        if (ref->Actual_group()) break;
        if (auto params = b->Parameters()) {
          for (auto decl : *params) {
            if (decl->VpiName() == name) {
              ref->Actual_group(decl);
              break;
            }
          }
        }
        if (ref->Actual_group()) break;
        VectorOfany* stmts = b->Stmts();
        if (stmts) {
          for (auto init : *stmts) {
            if (init->UhdmType() == uhdmassign_stmt) {
              assign_stmt* as = (assign_stmt*)init;
              const expr* lhs = as->Lhs();
              if (lhs->VpiName() == name) {
                if (lhs->UhdmType() == uhdmref_var) continue;
                if (lhs->UhdmType() == uhdmref_obj) continue;
                ref->Actual_group((expr*)lhs);
                break;
              }
            } else if (init->UhdmType() == uhdmassignment) {
              assignment* as = (assignment*)init;
              const expr* lhs = as->Lhs();
              if (lhs->VpiName() == name) {
                if (lhs->UhdmType() == uhdmref_var) continue;
                if (lhs->UhdmType() == uhdmref_obj) continue;
                ref->Actual_group((expr*)lhs);
                break;
              }
            }
          }
        }
      }
      if (ref->Actual_group()) break;
      parent = parent->VpiParent();
    }
    if (ref->Actual_group()) continue;
    if (m && (m->UhdmType() == uhdmmodule_inst)) {
      module_inst* minst = (module_inst*)m;
      if (minst->Interfaces()) {
        for (auto n : *minst->Interfaces()) {
          if (n->VpiName() == name) {
            ref->Actual_group(n);
            break;
          }
        }
        if (ref->Actual_group()) continue;
      }
      if (minst->Interface_arrays()) {
        for (auto n : *minst->Interface_arrays()) {
          if (n->VpiName() == name) {
            ref->Actual_group(n);
            break;
          }
        }
        if (ref->Actual_group()) continue;
      }
    }
    if (m &&
        (m->UhdmType() == uhdmmodule_inst ||
         m->UhdmType() == uhdminterface_inst || m->UhdmType() == uhdmprogram)) {
      instance* inst = (instance*)m;
      if (inst->Nets()) {
        for (auto n : *inst->Nets()) {
          if (n->VpiName() == name) {
            ref->Actual_group(n);
            break;
          }
          if (const ref_typespec* reftps = n->Typespec()) {
            const typespec* tps = reftps->Actual_typespec();
            if (tps->UhdmType() == uhdmenum_typespec) {
              const enum_typespec* etps = any_cast<const enum_typespec*>(tps);
              if (etps && etps->Enum_consts()) {
                for (auto c : *etps->Enum_consts()) {
                  if (c->VpiName() == name) {
                    ref->Actual_group(c);
                    break;
                  }
                }
                if (ref->Actual_group()) break;
              }
            }
          }
        }
        if (ref->Actual_group()) continue;
      }
      if (inst->Array_nets()) {
        for (auto n : *inst->Array_nets()) {
          if (n->VpiName() == name) {
            ref->Actual_group(n);
            break;
          }
        }
        if (ref->Actual_group()) continue;
      }
    }
    if (m && m->Variables()) {
      for (auto n : *m->Variables()) {
        if (n->VpiName() == name) {
          ref->Actual_group(n);
          break;
        }
        const std::string pname = StrCat(m->VpiName(), "::", name);
        if (n->VpiName() == pname) {
          ref->Actual_group(n);
          break;
        }
      }
      if (ref->Actual_group()) continue;
    }

    if (m && m->Param_assigns()) {
      bool isParam = false;
      for (auto p : *m->Param_assigns()) {
        const any* lhs = p->Lhs();
        if (lhs->VpiName() == name) {
          // Do not bind blindly here, let the uhdmelab do this correctly
          // Unless we are in a package
          if (m && m->UhdmType() == uhdmpackage) ref->Actual_group(p->Rhs());
          isParam = true;
          break;
        }
      }
      if (isParam) continue;
    }
    if (m && m->Parameters()) {
      bool isParam = false;
      for (auto p : *m->Parameters()) {
        if (p->VpiName() == name) {
          isParam = true;
          break;
        }
      }
      if (isParam) continue;
    }
    if (m && m->Property_decls()) {
      for (auto n : *m->Property_decls()) {
        if (n->VpiName() == name) {
          ref->Actual_group(n);
          break;
        }
      }
    }
    if (m && m->Sequence_decls()) {
      for (auto n : *m->Sequence_decls()) {
        if (n->VpiName() == name) {
          ref->Actual_group(n);
          break;
        }
      }
    }
    if (m && m->Typespecs()) {
      bool isTypespec = false;
      std::vector<std::string> importedPackages;
      for (auto n : *m->Typespecs()) {
        if (n->UhdmType() == uhdmimport_typespec) {
          importedPackages.emplace_back(n->VpiName());
        }
      }

      for (auto n : *m->Typespecs()) {
        if (n->UhdmType() == uhdmenum_typespec) {
          enum_typespec* tps = any_cast<enum_typespec*>(n);
          if (tps && tps->Enum_consts()) {
            for (auto c : *tps->Enum_consts()) {
              if (c->VpiName() == name) {
                ref->Actual_group(c);
                break;
              }
              if (std::string(std::string(m->VpiName()) + std::string("::") +
                              std::string(name)) == c->VpiName()) {
                ref->Actual_group(c);
                break;
              }
            }
          }
        }
        for (const auto& imp : importedPackages) {
          if (n->VpiName() == StrCat(imp, "::", name)) {
            isTypespec = true;
            break;
          }
        }
        if (n->VpiName() == name) {
          isTypespec = true;
          break;
        }
        if (ref->Actual_group()) break;
      }
      if (isTypespec) continue;
      if (ref->Actual_group()) continue;
    }
    const FileContent* fC = mod->getFileContents()[0];
    for (const auto& td : fC->getTypeDefMap()) {
      const DataType* dt = td.second;
      while (dt) {
        typespec* n = dt->getTypespec();
        n = replace(n, m_compileDesign->getSwapedObjects());
        if (n && (n->UhdmType() == uhdmenum_typespec)) {
          enum_typespec* tps = any_cast<enum_typespec*>(n);
          if (tps && tps->Enum_consts()) {
            for (auto c : *tps->Enum_consts()) {
              if (c->VpiName() == name) {
                ref->Actual_group(c);
                break;
              }
            }
          }
        }
        dt = dt->getDefinition();
        if (ref->Actual_group()) break;
      }
      if (ref->Actual_group()) break;
    }

    if (m && m->Variables()) {
      for (auto var : *m->Variables()) {
        if (var->UhdmType() == uhdmenum_var) {
          if (const ref_typespec* rt = var->Typespec()) {
            if (const enum_typespec* tps =
                    rt->Actual_typespec<enum_typespec>()) {
              if (tps->Enum_consts()) {
                for (auto c : *tps->Enum_consts()) {
                  if (c->VpiName() == name) {
                    ref->Actual_group(c);
                    break;
                  }
                }
              }
            }
          }
        }
        if (ref->Actual_group()) break;
      }
    }

    if (!ref->Actual_group()) {
      design* d = m_uhdmDesign;
      if (auto params = d->Parameters()) {
        for (auto decl : *params) {
          if (decl->VpiName() == name) {
            ref->Actual_group(decl);
            break;
          }
        }
      }
    }

    if (!ref->Actual_group()) {
      Value* value = mod->getValue(name);
      if (value && value->isValid()) {
        enum_const* c = s.MakeEnum_const();
        c->VpiName(name);
        c->VpiValue(value->uhdmValue());
        c->VpiDecompile(value->decompiledValue());
        c->VpiSize(value->getSize());
        c->VpiParent(ref);
        ref->Actual_group(c);
      }
    }
    if (!ref->Actual_group()) {
      if (mod) {
        if (auto elem = mod->getDesignElement()) {
          if (elem->m_defaultNetType == VObjectType::slNoType) {
            Location loc(fileSystem->toPathId(
                             ref->VpiFile(),
                             m_compileDesign->getCompiler()->getSymbolTable()),
                         ref->VpiLineNo(), ref->VpiColumnNo(),
                         m_compileDesign->getCompiler()
                             ->getSymbolTable()
                             ->registerSymbol(name));
            Error err(ErrorDefinition::ELAB_ILLEGAL_IMPLICIT_NET, loc);
            m_compileDesign->getCompiler()->getErrorContainer()->addError(err);
            m_compileDesign->getCompiler()->getErrorContainer()->printMessages(
                m_compileDesign->getCompiler()
                    ->getCommandLineParser()
                    ->muteStdout());
          } else {
            if (m && (m->UhdmType() == uhdmmodule_inst ||
                      m->UhdmType() == uhdminterface_inst ||
                      m->UhdmType() == uhdmprogram)) {
              instance* inst = (instance*)m;
              logic_net* net = s.MakeLogic_net();
              net->VpiName(name);
              net->VpiParent(m);
              net->VpiLineNo(ref->VpiLineNo());
              net->VpiColumnNo(ref->VpiColumnNo());
              net->VpiEndLineNo(ref->VpiEndLineNo());
              net->VpiEndColumnNo(ref->VpiEndColumnNo());
              net->VpiNetType(
                  UhdmWriter::getVpiNetType(elem->m_defaultNetType));
              net->VpiLineNo(ref->VpiLineNo());
              net->VpiEndLineNo(ref->VpiEndLineNo());
              net->VpiColumnNo(ref->VpiColumnNo());
              net->VpiEndColumnNo(ref->VpiEndColumnNo());
              ref->Actual_group(net);
              VectorOfnet* nets = inst->Nets();
              if (nets == nullptr) {
                inst->Nets(s.MakeNetVec());
                nets = inst->Nets();
              }
              nets->push_back(net);
            }
          }
        }
      }
    }
  }
}

bool UhdmWriter::writeElabModule(Serializer& s, ModuleInstance* instance,
                                 module_inst* m, ExprBuilder& exprBuilder) {
  Netlist* netlist = instance->getNetlist();
  if (netlist == nullptr) return true;
  m->Ports(netlist->ports());
  DesignComponent* mod = instance->getDefinition();
  if (mod) {
    // Let decls
    if (!mod->getLetStmts().empty()) {
      VectorOflet_decl* decls = s.MakeLet_declVec();
      m->Let_decls(decls);
      for (auto stmt : mod->getLetStmts()) {
        decls->push_back((let_decl*)stmt.second->Decl());
      }
    }
    if (!mod->getPropertyDecls().empty()) {
      VectorOfproperty_decl* decls = s.MakeProperty_declVec();
      m->Property_decls(decls);
      for (auto decl : mod->getPropertyDecls()) {
        decl->VpiParent(m);
        decls->push_back(decl);
      }
    }
    // Typepecs
    VectorOftypespec* typespecs = s.MakeTypespecVec();
    m->Typespecs(typespecs);
    writeDataTypes(mod->getDataTypeMap(), m, typespecs, s, false);
    writeImportedSymbols(mod, s, typespecs);
    // System elab tasks
    m->Elab_tasks((std::vector<UHDM::tf_call*>*)&mod->getElabSysCalls());
    if (m->Elab_tasks()) {
      for (auto et : *m->Elab_tasks()) {
        et->VpiParent(m);
      }
    }
    // Assertions
    if (mod->getAssertions()) {
      m->Assertions(mod->getAssertions());
      for (auto ps : *m->Assertions()) {
        ps->VpiParent(m);
      }
    }
  }

  writeElabParameters(s, instance, m, exprBuilder);
  if (netlist) {
    if (netlist->ports()) {
      for (auto obj : *netlist->ports()) {
        obj->VpiParent(m);
      }
    }
    m->Nets(netlist->nets());
    if (netlist->nets()) {
      for (auto obj : *netlist->nets()) {
        obj->VpiParent(m);
      }
    }
    m->Gen_scope_arrays(netlist->gen_scopes());
    if (netlist->gen_scopes()) {
      for (auto obj : *netlist->gen_scopes()) {
        obj->VpiParent(m);
      }
    }
    m->Variables(netlist->variables());
    if (netlist->variables()) {
      for (auto obj : *netlist->variables()) {
        obj->VpiParent(m);
      }
    }
    m->Array_vars(netlist->array_vars());
    if (netlist->array_vars()) {
      for (auto obj : *netlist->array_vars()) {
        obj->VpiParent(m);
      }
    }
    m->Named_events(netlist->named_events());
    if (netlist->named_events()) {
      for (auto obj : *netlist->named_events()) {
        obj->VpiParent(m);
      }
    }
    m->Array_nets(netlist->array_nets());
    if (netlist->array_nets()) {
      for (auto obj : *netlist->array_nets()) {
        obj->VpiParent(m);
      }
    }

    if (netlist->cont_assigns()) {
      std::vector<cont_assign*>* assigns = m->Cont_assigns();
      if (assigns == nullptr) {
        m->Cont_assigns(s.MakeCont_assignVec());
        assigns = m->Cont_assigns();
      }
      writeCont_assign(netlist, s, mod, m, assigns);
    }

    // Processes
    m->Process(netlist->process_stmts());
  }

  if (mod) {
    // ClockingBlocks
    ModuleDefinition* def = (ModuleDefinition*)mod;
    for (const auto& ctupple : def->getClockingBlockMap()) {
      const ClockingBlock& cblock = ctupple.second;
      ElaboratorContext elaboratorContext(&s, false, true);
      clocking_block* cb = (clocking_block*)UHDM::clone_tree(
          cblock.getActual(), &elaboratorContext);
      cb->VpiParent(m);
      switch (cblock.getType()) {
        case ClockingBlock::Type::Default: {
          m->Default_clocking(cb);
          break;
        }
        case ClockingBlock::Type::Global: {
          m->Global_clocking(cb);
          break;
        }
        case ClockingBlock::Type::Regular: {
          VectorOfclocking_block* cblocks = m->Clocking_blocks();
          if (cblocks == nullptr) {
            m->Clocking_blocks(s.MakeClocking_blockVec());
            cblocks = m->Clocking_blocks();
          }
          cblocks->push_back(cb);
          break;
        }
      }
    }
  }

  if (mod) {
    if (auto from = mod->getTask_funcs()) {
      UHDM::VectorOftask_func* target = m->Task_funcs();
      if (target == nullptr) {
        m->Task_funcs(s.MakeTask_funcVec());
        target = m->Task_funcs();
      }
      for (auto tf : *from) {
        target->push_back(tf);
        if (tf->VpiParent() == nullptr) tf->VpiParent(m);
        if (tf->Instance() == nullptr) tf->Instance(m);
      }
    }
  }
  return true;
}

bool UhdmWriter::writeElabInterface(Serializer& s, ModuleInstance* instance,
                                    interface_inst* m,
                                    ExprBuilder& exprBuilder) {
  Netlist* netlist = instance->getNetlist();
  DesignComponent* mod = instance->getDefinition();
  if (mod) {
    // Let decls
    if (!mod->getLetStmts().empty()) {
      VectorOflet_decl* decls = s.MakeLet_declVec();
      m->Let_decls(decls);
      for (auto stmt : mod->getLetStmts()) {
        decls->push_back((let_decl*)stmt.second->Decl());
      }
    }
    if (!mod->getPropertyDecls().empty()) {
      VectorOfproperty_decl* decls = s.MakeProperty_declVec();
      m->Property_decls(decls);
      for (auto decl : mod->getPropertyDecls()) {
        decl->VpiParent(m);
        decls->push_back(decl);
      }
    }
    // Typepecs
    VectorOftypespec* typespecs = s.MakeTypespecVec();
    m->Typespecs(typespecs);
    writeDataTypes(mod->getDataTypeMap(), m, typespecs, s, false);
    writeImportedSymbols(mod, s, typespecs);
    // System elab tasks
    m->Elab_tasks((std::vector<UHDM::tf_call*>*)&mod->getElabSysCalls());
    if (m->Elab_tasks()) {
      for (auto et : *m->Elab_tasks()) {
        et->VpiParent(m);
      }
    }
    // Assertions
    if (mod->getAssertions()) {
      m->Assertions(mod->getAssertions());
      for (auto ps : *m->Assertions()) {
        ps->VpiParent(m);
      }
    }
  }

  writeElabParameters(s, instance, m, exprBuilder);
  if (netlist) {
    m->Ports(netlist->ports());
    if (netlist->ports()) {
      for (auto obj : *netlist->ports()) {
        obj->VpiParent(m);
      }
    }
    m->Nets(netlist->nets());
    if (netlist->nets()) {
      for (auto obj : *netlist->nets()) {
        obj->VpiParent(m);
      }
    }
    m->Gen_scope_arrays(netlist->gen_scopes());
    if (netlist->gen_scopes()) {
      for (auto obj : *netlist->gen_scopes()) {
        obj->VpiParent(m);
      }
    }
    m->Variables(netlist->variables());
    if (netlist->variables()) {
      for (auto obj : *netlist->variables()) {
        obj->VpiParent(m);
      }
    }
    m->Array_vars(netlist->array_vars());
    if (netlist->array_vars()) {
      for (auto obj : *netlist->array_vars()) {
        obj->VpiParent(m);
      }
    }
    m->Named_events(netlist->named_events());
    if (netlist->named_events()) {
      for (auto obj : *netlist->named_events()) {
        obj->VpiParent(m);
      }
    }
    m->Array_nets(netlist->array_nets());
    if (netlist->array_nets()) {
      for (auto obj : *netlist->array_nets()) {
        obj->VpiParent(m);
      }
    }
  }

  if (netlist) {
    if (netlist->cont_assigns()) {
      std::vector<cont_assign*>* assigns = m->Cont_assigns();
      if (assigns == nullptr) {
        m->Cont_assigns(s.MakeCont_assignVec());
        assigns = m->Cont_assigns();
      }
      writeCont_assign(netlist, s, mod, m, assigns);
    }

    // Processes
    m->Process(netlist->process_stmts());
  }

  // Modports
  ModuleDefinition* module = (ModuleDefinition*)mod;
  ModuleDefinition::ModPortSignalMap& orig_modports =
      module->getModPortSignalMap();
  VectorOfmodport* dest_modports = s.MakeModportVec();
  for (auto& orig_modport : orig_modports) {
    modport* dest_modport = s.MakeModport();
    dest_modport->Interface_inst(m);
    dest_modport->VpiName(orig_modport.first);
    dest_modport->VpiParent(m);
    const FileContent* orig_fC = orig_modport.second.getFileContent();
    const NodeId orig_nodeId = orig_modport.second.getNodeId();
    orig_fC->populateCoreMembers(orig_nodeId, orig_nodeId, dest_modport);
    VectorOfio_decl* ios = s.MakeIo_declVec();
    for (auto& sig : orig_modport.second.getPorts()) {
      const FileContent* fC = sig.getFileContent();
      io_decl* io = s.MakeIo_decl();
      io->VpiName(sig.getName());
      NodeId id = sig.getNodeId();
      fC->populateCoreMembers(id, id, io);
      if (NodeId Expression = fC->Sibling(id)) {
        m_helper.checkForLoops(true);
        any* exp =
            m_helper.compileExpression(mod, fC, Expression, m_compileDesign,
                                       Reduce::Yes, io, instance, true);
        m_helper.checkForLoops(false);
        io->Expr(exp);
      }
      uint32_t direction = UhdmWriter::getVpiDirection(sig.getDirection());
      io->VpiDirection(direction);
      io->VpiParent(dest_modport);
      ios->push_back(io);
    }
    dest_modport->Io_decls(ios);
    dest_modports->push_back(dest_modport);
  }
  m->Modports(dest_modports);

  if (mod) {
    // ClockingBlocks
    ModuleDefinition* def = (ModuleDefinition*)mod;
    for (const auto& ctupple : def->getClockingBlockMap()) {
      const ClockingBlock& cblock = ctupple.second;
      ElaboratorContext elaboratorContext(&s, false, true);
      clocking_block* cb = (clocking_block*)UHDM::clone_tree(
          cblock.getActual(), &elaboratorContext);
      cb->VpiParent(m);
      switch (cblock.getType()) {
        case ClockingBlock::Type::Default: {
          m->Default_clocking(cb);
          break;
        }
        case ClockingBlock::Type::Global: {
          m->Global_clocking(cb);
          break;
        }
        case ClockingBlock::Type::Regular: {
          VectorOfclocking_block* cblocks = m->Clocking_blocks();
          if (cblocks == nullptr) {
            m->Clocking_blocks(s.MakeClocking_blockVec());
            cblocks = m->Clocking_blocks();
          }
          cblocks->push_back(cb);
          break;
        }
      }
    }
  }

  if (mod) {
    if (auto from = mod->getTask_funcs()) {
      UHDM::VectorOftask_func* target = m->Task_funcs();
      if (target == nullptr) {
        m->Task_funcs(s.MakeTask_funcVec());
        target = m->Task_funcs();
      }
      for (auto tf : *from) {
        target->push_back(tf);
        if (tf->VpiParent() == nullptr) tf->VpiParent(m);
        if (tf->Instance() == nullptr) tf->Instance(m);
      }
    }
  }
  return true;
}

void writePrimTerms(ModuleInstance* instance, primitive* prim,
                    int32_t vpiGateType, Serializer& s) {
  Netlist* netlist = instance->getNetlist();
  VectorOfprim_term* terms = s.MakePrim_termVec();
  prim->Prim_terms(terms);
  if (netlist->ports()) {
    uint32_t index = 0;
    VectorOfport* ports = netlist->ports();
    for (auto port : *ports) {
      prim_term* term = s.MakePrim_term();
      terms->push_back(term);
      expr* hconn = (expr*)port->High_conn();
      hconn->VpiParent(prim);
      term->Expr(hconn);
      term->VpiFile(port->VpiFile());
      term->VpiLineNo(port->VpiLineNo());
      term->VpiColumnNo(port->VpiColumnNo());
      term->VpiEndLineNo(port->VpiEndLineNo());
      term->VpiEndColumnNo(port->VpiEndColumnNo());
      term->VpiDirection(port->VpiDirection());
      term->VpiParent(prim);
      term->VpiTermIndex(index);
      if (vpiGateType == vpiBufPrim || vpiGateType == vpiNotPrim) {
        if (index < ports->size() - 1) {
          term->VpiDirection(vpiOutput);
        } else {
          term->VpiDirection(vpiInput);
        }
      } else if (vpiGateType == vpiTranif1Prim ||
                 vpiGateType == vpiTranif0Prim ||
                 vpiGateType == vpiRtranif1Prim ||
                 vpiGateType == vpiRtranif0Prim || vpiGateType == vpiTranPrim ||
                 vpiGateType == vpiRtranPrim) {
        if (index < ports->size() - 1) {
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
    }
  }
}

void UhdmWriter::writeInstance(ModuleDefinition* mod, ModuleInstance* instance,
                               any* m, CompileDesign* compileDesign,
                               ModPortMap& modPortMap, InstanceMap& instanceMap,
                               ExprBuilder& exprBuilder) {
  FileSystem* const fileSystem = FileSystem::getInstance();
  Serializer& s = compileDesign->getSerializer();
  VectorOfmodule_inst* subModules = nullptr;
  VectorOfprogram* subPrograms = nullptr;
  VectorOfinterface_inst* subInterfaces = nullptr;
  VectorOfprimitive* subPrimitives = nullptr;
  VectorOfprimitive_array* subPrimitiveArrays = nullptr;
  VectorOfgen_scope_array* subGenScopeArrays = nullptr;
  m_componentMap.emplace(instance, m);
  if (m->UhdmType() == uhdmmodule_inst) {
    writeElabModule(s, instance, (module_inst*)m, exprBuilder);
  } else if (m->UhdmType() == uhdmgen_scope) {
    writeElabGenScope(s, instance, (gen_scope*)m, exprBuilder);
  } else if (m->UhdmType() == uhdminterface_inst) {
    writeElabInterface(s, instance, (interface_inst*)m, exprBuilder);
  }
  Netlist* netlist = instance->getNetlist();
  if (netlist) {
    if (VectorOfinterface_array* subInterfaceArrays =
            netlist->interface_arrays()) {
      UHDM_OBJECT_TYPE utype = m->UhdmType();
      if (utype == uhdmmodule_inst) {
        ((module_inst*)m)->Interface_arrays(subInterfaceArrays);
        for (interface_array* array : *subInterfaceArrays) {
          array->VpiParent(m);
        }
      } else if (utype == uhdmgen_scope) {
        ((gen_scope*)m)->Interface_arrays(subInterfaceArrays);
        for (interface_array* array : *subInterfaceArrays) {
          array->VpiParent(m);
        }
      } else if (utype == uhdminterface_inst) {
        ((interface_inst*)m)->Interface_arrays(subInterfaceArrays);
        for (interface_array* array : *subInterfaceArrays) {
          array->VpiParent(m);
        }
      }
    }
    if (VectorOfinterface_inst* subInterfaces = netlist->interfaces()) {
      UHDM_OBJECT_TYPE utype = m->UhdmType();
      if (utype == uhdmmodule_inst) {
        ((module_inst*)m)->Interfaces(subInterfaces);
        for (interface_inst* interf : *subInterfaces) {
          interf->VpiParent(m);
        }
      } else if (utype == uhdmgen_scope) {
        ((gen_scope*)m)->Interfaces(subInterfaces);
        for (interface_inst* interf : *subInterfaces) {
          interf->VpiParent(m);
        }
      } else if (utype == uhdminterface_inst) {
        ((interface_inst*)m)->Interfaces(subInterfaces);
        for (interface_inst* interf : *subInterfaces) {
          interf->VpiParent(m);
        }
      }
    }
  }
  std::map<ModuleInstance*, module_inst*> tempInstanceMap;
  for (uint32_t i = 0; i < instance->getNbChildren(); i++) {
    ModuleInstance* child = instance->getChildren(i);
    DesignComponent* childDef = child->getDefinition();
    if (ModuleDefinition* mm =
            valuedcomponenti_cast<ModuleDefinition*>(childDef)) {
      VObjectType insttype = child->getType();
      if (insttype == VObjectType::paModule_instantiation) {
        if (subModules == nullptr) subModules = s.MakeModule_instVec();
        module_inst* sm = s.MakeModule_inst();
        tempInstanceMap.emplace(child, sm);
        if (childDef && !childDef->getFileContents().empty() &&
            compileDesign->getCompiler()->isLibraryFile(
                childDef->getFileContents()[0]->getFileId())) {
          sm->VpiCellInstance(true);
        }
        sm->VpiName(child->getInstanceName());
        sm->VpiDefName(child->getModuleName());
        sm->VpiFullName(child->getFullPathName());
        const FileContent* defFile = mm->getFileContents()[0];
        sm->VpiDefFile(fileSystem->toPath(defFile->getFileId()));
        sm->VpiDefLineNo(defFile->Line(mm->getNodeIds()[0]));
        child->getFileContent()->populateCoreMembers(child->getNodeId(),
                                                     child->getNodeId(), sm);
        subModules->push_back(sm);
        if (m->UhdmType() == uhdmmodule_inst) {
          ((module_inst*)m)->Modules(subModules);
          sm->Instance((module_inst*)m);
          sm->Module_inst((module_inst*)m);
          sm->VpiParent(m);
        } else if (m->UhdmType() == uhdmgen_scope) {
          ((gen_scope*)m)->Modules(subModules);
          sm->VpiParent(m);
        }
        writeInstance(mm, child, sm, compileDesign, modPortMap, instanceMap,
                      exprBuilder);
      } else if (insttype == VObjectType::paConditional_generate_construct ||
                 insttype == VObjectType::paLoop_generate_construct ||
                 insttype == VObjectType::paGenerate_begin_end_block ||
                 insttype == VObjectType::paGenerate_item ||
                 insttype == VObjectType::paGenerate_region ||
                 insttype == VObjectType::paGenerate_module_loop_statement ||
                 insttype ==
                     VObjectType::paGenerate_module_conditional_statement ||
                 insttype == VObjectType::paGenerate_module_block ||
                 insttype == VObjectType::paGenerate_module_item ||
                 insttype == VObjectType::paGenerate_module_named_block ||
                 insttype == VObjectType::paGenerate_module_block ||
                 insttype == VObjectType::paGenerate_module_item ||
                 insttype == VObjectType::paGenerate_interface_loop_statement ||
                 insttype ==
                     VObjectType::paGenerate_interface_conditional_statement ||
                 insttype == VObjectType::paGenerate_interface_block ||
                 insttype == VObjectType::paGenerate_interface_item ||
                 insttype == VObjectType::paGenerate_interface_named_block ||
                 insttype == VObjectType::paGenerate_interface_block ||
                 insttype == VObjectType::paGenerate_interface_item) {
        if (subGenScopeArrays == nullptr)
          subGenScopeArrays = s.MakeGen_scope_arrayVec();
        gen_scope_array* sm = s.MakeGen_scope_array();
        sm->VpiName(child->getInstanceName());
        sm->VpiFullName(child->getFullPathName());
        child->getFileContent()->populateCoreMembers(child->getNodeId(),
                                                     child->getNodeId(), sm);
        subGenScopeArrays->push_back(sm);
        gen_scope* a_gen_scope = s.MakeGen_scope();
        sm->Gen_scopes(s.MakeGen_scopeVec());
        sm->Gen_scopes()->push_back(a_gen_scope);
        child->getFileContent()->populateCoreMembers(
            child->getNodeId(), child->getNodeId(), a_gen_scope);
        a_gen_scope->VpiParent(sm);
        UHDM_OBJECT_TYPE utype = m->UhdmType();
        if (utype == uhdmmodule_inst) {
          ((module_inst*)m)->Gen_scope_arrays(subGenScopeArrays);
          sm->VpiParent(m);
        } else if (utype == uhdmgen_scope) {
          ((gen_scope*)m)->Gen_scope_arrays(subGenScopeArrays);
          sm->VpiParent(m);
        } else if (utype == uhdminterface_inst) {
          ((interface_inst*)m)->Gen_scope_arrays(subGenScopeArrays);
          sm->VpiParent(m);
        }
        writeInstance(mm, child, a_gen_scope, compileDesign, modPortMap,
                      instanceMap, exprBuilder);

      } else if (insttype == VObjectType::paInterface_instantiation) {
        if (subInterfaces == nullptr) subInterfaces = s.MakeInterface_instVec();
        interface_inst* sm = s.MakeInterface_inst();
        sm->VpiName(child->getInstanceName());
        sm->VpiDefName(child->getModuleName());
        sm->VpiFullName(child->getFullPathName());
        child->getFileContent()->populateCoreMembers(child->getNodeId(),
                                                     child->getNodeId(), sm);
        const FileContent* defFile = mm->getFileContents()[0];
        sm->VpiDefFile(fileSystem->toPath(defFile->getFileId()));
        sm->VpiDefLineNo(defFile->Line(mm->getNodeIds()[0]));
        subInterfaces->push_back(sm);
        UHDM_OBJECT_TYPE utype = m->UhdmType();
        if (utype == uhdmmodule_inst) {
          ((module_inst*)m)->Interfaces(subInterfaces);
          sm->Instance((module_inst*)m);
          sm->VpiParent(m);
        } else if (utype == uhdmgen_scope) {
          ((gen_scope*)m)->Interfaces(subInterfaces);
          sm->VpiParent(m);
        } else if (utype == uhdminterface_inst) {
          ((interface_inst*)m)->Interfaces(subInterfaces);
          sm->VpiParent(m);
        }
        writeInstance(mm, child, sm, compileDesign, modPortMap, instanceMap,
                      exprBuilder);

      } else if ((insttype == VObjectType::paUdp_instantiation) ||
                 (insttype == VObjectType::paCmos_switch_instance) ||
                 (insttype == VObjectType::paEnable_gate_instance) ||
                 (insttype == VObjectType::paMos_switch_instance) ||
                 (insttype == VObjectType::paN_input_gate_instance) ||
                 (insttype == VObjectType::paN_output_gate_instance) ||
                 (insttype == VObjectType::paPass_enable_switch_instance) ||
                 (insttype == VObjectType::paPass_switch_instance) ||
                 (insttype == VObjectType::paPull_gate_instance)) {
        UHDM::primitive* gate = nullptr;
        UHDM::primitive_array* gate_array = nullptr;
        const FileContent* fC = child->getFileContent();
        NodeId gatenode = fC->Child(fC->Parent(child->getNodeId()));
        VObjectType gatetype = fC->Type(gatenode);
        int32_t vpiGateType = m_helper.getBuiltinType(gatetype);
        if (insttype == VObjectType::paUdp_instantiation) {
          UHDM::udp* udp = s.MakeUdp();
          gate = udp;
          if (ModuleDefinition* mm =
                  valuedcomponenti_cast<ModuleDefinition*>(childDef)) {
            udp->Udp_defn(mm->getUdpDefn());
          }
          if (UHDM::VectorOfrange* ranges = child->getNetlist()->ranges()) {
            gate_array = s.MakeUdp_array();
            VectorOfprimitive* prims = s.MakePrimitiveVec();
            gate_array->Primitives(prims);
            gate_array->Ranges(ranges);
            gate_array->VpiParent(m);
            prims->push_back(gate);
            gate->VpiParent(gate_array);
            for (auto r : *ranges) r->VpiParent(gate_array);
            if (subPrimitiveArrays == nullptr)
              subPrimitiveArrays = s.MakePrimitive_arrayVec();
            subPrimitiveArrays->push_back(gate_array);
          } else {
            if (subPrimitives == nullptr) subPrimitives = s.MakePrimitiveVec();
            subPrimitives->push_back(gate);
          }
        } else if (vpiGateType == vpiPmosPrim || vpiGateType == vpiRpmosPrim ||
                   vpiGateType == vpiNmosPrim || vpiGateType == vpiRnmosPrim ||
                   vpiGateType == vpiCmosPrim || vpiGateType == vpiRcmosPrim ||
                   vpiGateType == vpiTranif1Prim ||
                   vpiGateType == vpiTranif0Prim ||
                   vpiGateType == vpiRtranif1Prim ||
                   vpiGateType == vpiRtranif0Prim ||
                   vpiGateType == vpiTranPrim || vpiGateType == vpiRtranPrim) {
          gate = s.MakeSwitch_tran();
          if (UHDM::VectorOfrange* ranges = child->getNetlist()->ranges()) {
            gate_array = s.MakeSwitch_array();
            VectorOfprimitive* prims = s.MakePrimitiveVec();
            gate_array->Primitives(prims);
            gate_array->Ranges(ranges);
            gate_array->VpiParent(m);
            prims->push_back(gate);
            gate->VpiParent(gate_array);
            for (auto r : *ranges) r->VpiParent(gate_array);
            if (subPrimitiveArrays == nullptr)
              subPrimitiveArrays = s.MakePrimitive_arrayVec();
            subPrimitiveArrays->push_back(gate_array);
          } else {
            if (subPrimitives == nullptr) subPrimitives = s.MakePrimitiveVec();
            subPrimitives->push_back(gate);
          }
          gate->VpiPrimType(vpiGateType);
        } else {
          gate = s.MakeGate();
          if (UHDM::VectorOfrange* ranges = child->getNetlist()->ranges()) {
            gate_array = s.MakeGate_array();
            gate_array->VpiName(child->getInstanceName());
            gate_array->VpiFullName(child->getFullPathName());
            child->getFileContent()->populateCoreMembers(
                child->getNodeId(), child->getNodeId(), gate_array);
            VectorOfprimitive* prims = s.MakePrimitiveVec();
            gate_array->Primitives(prims);
            gate_array->Ranges(ranges);
            gate_array->VpiParent(m);
            prims->push_back(gate);
            gate->VpiParent(gate_array);
            for (auto r : *ranges) r->VpiParent(gate_array);
            if (subPrimitiveArrays == nullptr)
              subPrimitiveArrays = s.MakePrimitive_arrayVec();
            subPrimitiveArrays->push_back(gate_array);
          } else {
            if (subPrimitives == nullptr) subPrimitives = s.MakePrimitiveVec();
            subPrimitives->push_back(gate);
          }
          gate->VpiPrimType(vpiGateType);
        }
        if (UHDM::VectorOfexpr* delays = child->getNetlist()->delays()) {
          if (delays->size() == 1) {
            gate->Delay((*delays)[0]);
          }
        }

        gate->VpiName(child->getInstanceName());
        gate->VpiDefName(child->getModuleName());
        gate->VpiFullName(child->getFullPathName());
        child->getFileContent()->populateCoreMembers(child->getNodeId(),
                                                     child->getNodeId(), gate);
        UHDM_OBJECT_TYPE utype = m->UhdmType();
        if (utype == uhdmmodule_inst) {
          ((module_inst*)m)->Primitives(subPrimitives);
          ((module_inst*)m)->Primitive_arrays(subPrimitiveArrays);
          m_helper.setParentNoOverride(gate, m);
        } else if (utype == uhdmgen_scope) {
          ((gen_scope*)m)->Primitives(subPrimitives);
          ((gen_scope*)m)->Primitive_arrays(subPrimitiveArrays);
          m_helper.setParentNoOverride(gate, m);
        }
        writePrimTerms(child, gate, vpiGateType, s);
      } else {
        // Unknown object type
      }
    } else if (Program* prog = valuedcomponenti_cast<Program*>(childDef)) {
      if (subPrograms == nullptr) subPrograms = s.MakeProgramVec();
      program* sm = s.MakeProgram();
      sm->VpiName(child->getInstanceName());
      sm->VpiDefName(child->getModuleName());
      sm->VpiFullName(child->getFullPathName());
      child->getFileContent()->populateCoreMembers(child->getNodeId(),
                                                   child->getNodeId(), sm);
      const FileContent* defFile = prog->getFileContents()[0];
      sm->VpiDefFile(fileSystem->toPath(defFile->getFileId()));
      sm->VpiDefLineNo(defFile->Line(prog->getNodeIds()[0]));
      subPrograms->push_back(sm);
      UHDM_OBJECT_TYPE utype = m->UhdmType();
      if (utype == uhdmmodule_inst) {
        ((module_inst*)m)->Programs(subPrograms);
        sm->Instance((module_inst*)m);
        sm->VpiParent(m);
      } else if (utype == uhdmgen_scope) {
        ((gen_scope*)m)->Programs(subPrograms);
        sm->VpiParent(m);
      }
      writeElabProgram(s, child, sm, modPortMap);
    } else {
      // Undefined module
      if (subModules == nullptr) subModules = s.MakeModule_instVec();
      module_inst* sm = s.MakeModule_inst();
      sm->VpiName(child->getInstanceName());
      sm->VpiDefName(child->getModuleName());
      sm->VpiFullName(child->getFullPathName());
      child->getFileContent()->populateCoreMembers(child->getNodeId(),
                                                   child->getNodeId(), sm);
      subModules->push_back(sm);
      UHDM_OBJECT_TYPE utype = m->UhdmType();
      if (utype == uhdmmodule_inst) {
        ((module_inst*)m)->Modules(subModules);
        sm->Instance((module_inst*)m);
        sm->Module_inst((module_inst*)m);
        sm->VpiParent(m);
      } else if (utype == uhdmgen_scope) {
        ((gen_scope*)m)->Modules(subModules);
        sm->VpiParent(m);
      }
      writeInstance(mm, child, sm, compileDesign, modPortMap, instanceMap,
                    exprBuilder);
    }
  }

  if (m->UhdmType() == uhdmmodule_inst) {
    const auto& moduleArrayModuleInstancesMap =
        instance->getModuleArrayModuleInstancesMap();
    if (!moduleArrayModuleInstancesMap.empty()) {
      ((module_inst*)m)->Module_arrays(s.MakeModule_arrayVec());
      std::vector<UHDM::module_array*> moduleArrays;
      std::transform(
          moduleArrayModuleInstancesMap.begin(),
          moduleArrayModuleInstancesMap.end(), std::back_inserter(moduleArrays),
          [](ModuleInstance::ModuleArrayModuleInstancesMap::const_reference
                 pair) { return pair.first; });
      std::sort(
          moduleArrays.begin(), moduleArrays.end(),
          [](const UHDM::module_array* lhs, const UHDM::module_array* rhs) {
            return lhs->UhdmId() < rhs->UhdmId();
          });
      for (UHDM::module_array* modArray : moduleArrays) {
        const auto& modInstances =
            moduleArrayModuleInstancesMap.find(modArray)->second;
        if (!modInstances.empty()) {
          modArray->Modules(s.MakeModule_instVec());
          modArray->VpiParent(m);
          ((module_inst*)m)->Module_arrays()->push_back(modArray);
          for (ModuleInstance* modInst : modInstances) {
            auto it = tempInstanceMap.find(modInst);
            if (it != tempInstanceMap.end()) {
              modArray->Modules()->push_back(it->second);
            }
          }
        }
      }
    }
  }

  if (mod && netlist) {
    if (scope* sc = any_cast<scope*>(m)) {
      lateTypedefBinding(s, mod, sc);
      lateBinding(s, mod, sc);
      lateTypedefBinding(s, mod, sc);
    }
  }
}

vpiHandle UhdmWriter::write(PathId uhdmFileId) {
  FileSystem* const fileSystem = FileSystem::getInstance();
  ModPortMap modPortMap;
  InstanceMap instanceMap;
  ModuleMap moduleMap;
  Serializer& s = m_compileDesign->getSerializer();
  ExprBuilder exprBuilder;
  exprBuilder.seterrorReporting(
      m_compileDesign->getCompiler()->getErrorContainer(),
      m_compileDesign->getCompiler()->getSymbolTable());

  Location loc(uhdmFileId);
  Error err(ErrorDefinition::UHDM_CREATING_MODEL, loc);
  m_compileDesign->getCompiler()->getErrorContainer()->addError(err);
  m_compileDesign->getCompiler()->getErrorContainer()->printMessages(
      m_compileDesign->getCompiler()->getCommandLineParser()->muteStdout());

  m_helper.setElabMode(false);

  // Compute list of design components that are part of the instance tree
  std::set<DesignComponent*> designComponents;
  {
    std::queue<ModuleInstance*> queue;
    for (const auto& pack : m_design->getPackageDefinitions()) {
      if (!pack.second->getFileContents().empty()) {
        if (pack.second->getFileContents()[0] != nullptr)
          designComponents.insert(pack.second);
      }
    }
    for (auto instance : m_design->getTopLevelModuleInstances()) {
      queue.push(instance);
    }

    while (!queue.empty()) {
      ModuleInstance* current = queue.front();
      DesignComponent* def = current->getDefinition();
      queue.pop();
      if (current == nullptr) continue;
      for (ModuleInstance* sub : current->getAllSubInstances()) {
        queue.push(sub);
      }
      const FileContent* fC = current->getFileContent();
      if (fC) {
        designComponents.insert(def);
      }
    }
  }

  vpiHandle designHandle = nullptr;
  std::vector<vpiHandle> designs;
  design* d = nullptr;
  if (m_design) {
    d = s.MakeDesign();
    m_uhdmDesign = d;
    designHandle = reinterpret_cast<vpiHandle>(new uhdm_handle(uhdmdesign, d));
    std::string designName = "unnamed";
    auto topLevelModules = m_design->getTopLevelModuleInstances();
    if (!topLevelModules.empty()) {
      designName = topLevelModules.front()->getModuleName();
    }
    d->VpiName(designName);
    designs.push_back(designHandle);

    // ---------------------------
    // Include File Info
    if (m_compileDesign->getFileInfo()) {
      d->Include_file_infos(m_compileDesign->getFileInfo());
      for (auto ifi : *m_compileDesign->getFileInfo()) {
        ifi->VpiParent(d);
      }
    }

    // -------------------------------
    // Non-Elaborated Model

    // FileContent
    VectorOftypespec* typespecs = s.MakeTypespecVec();
    d->Typespecs(typespecs);
    for (auto& fileIdContent : m_design->getAllFileContents()) {
      // Typepecs
      writeDataTypes(fileIdContent.second->getDataTypeMap(), d, typespecs, s,
                     true);

      // Function and tasks
      if (auto from = fileIdContent.second->getTask_funcs()) {
        UHDM::VectorOftask_func* target = d->Task_funcs();
        if (target == nullptr) {
          d->Task_funcs(s.MakeTask_funcVec());
          target = d->Task_funcs();
        }
        for (auto tf : *from) {
          target->push_back(tf);
          if (tf->VpiParent() == nullptr) tf->VpiParent(d);
        }
      }

      // Parameters
      if (auto from = fileIdContent.second->getParameters()) {
        UHDM::VectorOfany* target = d->Parameters();
        if (target == nullptr) {
          d->Parameters(s.MakeAnyVec());
          target = d->Parameters();
        }
        for (auto tf : *from) {
          tf->VpiParent(d);
          target->push_back(tf);
        }
      }

      // Param assigns
      if (auto from = fileIdContent.second->getParam_assigns()) {
        UHDM::VectorOfparam_assign* target = d->Param_assigns();
        if (target == nullptr) {
          d->Param_assigns(s.MakeParam_assignVec());
          target = d->Param_assigns();
        }
        for (auto tf : *from) {
          tf->VpiParent(d);
          target->push_back(tf);
        }
      }
      lateTypedefBinding(s, fileIdContent.second, nullptr);
    }

    // Packages
    SURELOG::PackageDefinitionVec packages =
        m_design->getOrderedPackageDefinitions();
    for (auto& pack : m_design->getPackageDefinitions()) {
      if (pack.first == "builtin") {
        if (pack.second) packages.insert(packages.begin(), pack.second);
        break;
      }
    }

    m_helper.setElabMode(true);

    VectorOfpackage* v2 = s.MakePackageVec();
    for (Package* pack : packages) {
      if (!pack) continue;
      if (!pack->getFileContents().empty() &&
          pack->getType() == VObjectType::paPackage_declaration) {
        const FileContent* fC = pack->getFileContents()[0];
        package* p = (package*)pack->getUhdmInstance();
        m_componentMap.emplace(pack, p);
        p->VpiParent(d);
        p->VpiTop(true);
        p->VpiDefName(pack->getName());
        if (pack->Attributes() != nullptr) {
          p->Attributes(pack->Attributes());
          for (auto a : *p->Attributes()) {
            a->VpiParent(p);
          }
        }
        writePackage(pack, p, s, true);
        if (fC) {
          // Builtin package has no file
          const NodeId modId = pack->getNodeIds()[0];
          const NodeId startId = fC->sl_collect(modId, VObjectType::paPACKAGE);
          fC->populateCoreMembers(startId, modId, p);
        }
        v2->push_back(p);
      }
    }
    d->TopPackages(v2);

    m_helper.setElabMode(false);

    VectorOfpackage* v3 = s.MakePackageVec();
    d->AllPackages(v3);
    for (Package* pack : packages) {
      if (!pack) continue;
      if (!pack->getFileContents().empty() &&
          pack->getType() == VObjectType::paPackage_declaration) {
        const FileContent* fC = pack->getFileContents()[0];
        package* p =
            any_cast<package*>(pack->getUnElabPackage()->getUhdmInstance());
        if (p == nullptr) p = s.MakePackage();
        m_componentMap.emplace(pack->getUnElabPackage(), p);
        p->VpiName(pack->getName());
        p->VpiParent(d);
        p->VpiDefName(pack->getName());
        if (pack->Attributes() != nullptr) {
          p->Attributes(pack->Attributes());
          for (auto a : *p->Attributes()) {
            a->VpiParent(p);
          }
        }
        v3->push_back(p);
        writePackage(pack->getUnElabPackage(), p, s, false);
        if (fC) {
          // Builtin package has no file
          const NodeId modId = pack->getNodeIds()[0];
          const NodeId startId = fC->sl_collect(modId, VObjectType::paPACKAGE);
          fC->populateCoreMembers(startId, modId, p);
        }
      }
    }

    // FileContent Late Binding after Packages
    for (auto& fileIdContent : m_design->getAllFileContents()) {
      lateTypedefBinding(s, fileIdContent.second, nullptr);
    }

    // Programs
    auto programs = m_design->getProgramDefinitions();
    VectorOfprogram* uhdm_programs = s.MakeProgramVec();
    for (const auto& progNamePair : programs) {
      Program* prog = progNamePair.second;
      if (!prog->getFileContents().empty() &&
          prog->getType() == VObjectType::paProgram_declaration) {
        const FileContent* fC = prog->getFileContents()[0];
        program* p = s.MakeProgram();
        m_componentMap.emplace(prog, p);
        moduleMap.emplace(prog->getName(), p);
        p->VpiParent(d);
        p->VpiDefName(prog->getName());
        const NodeId modId = prog->getNodeIds()[0];
        const NodeId startId = fC->sl_collect(modId, VObjectType::paPROGRAM);
        fC->populateCoreMembers(startId, modId, p);
        if (prog->Attributes() != nullptr) {
          p->Attributes(prog->Attributes());
          for (auto a : *p->Attributes()) {
            a->VpiParent(p);
          }
        }
        writeProgram(prog, p, s, modPortMap);
        uhdm_programs->push_back(p);
      }
    }
    d->AllPrograms(uhdm_programs);

    // Interfaces
    auto modules = m_design->getModuleDefinitions();
    VectorOfinterface_inst* uhdm_interfaces = s.MakeInterface_instVec();
    for (const auto& modNamePair : modules) {
      ModuleDefinition* mod = modNamePair.second;
      if (mod->getFileContents().empty()) {
        // Built-in primitive
      } else if (mod->getType() == VObjectType::paInterface_declaration) {
        const FileContent* fC = mod->getFileContents()[0];
        interface_inst* m = s.MakeInterface_inst();
        m_componentMap.emplace(mod, m);
        moduleMap.emplace(mod->getName(), m);
        m->VpiParent(d);
        m->VpiDefName(mod->getName());
        const NodeId modId = mod->getNodeIds()[0];
        const NodeId startId = fC->sl_collect(modId, VObjectType::paINTERFACE);
        fC->populateCoreMembers(startId, modId, m);
        if (mod->Attributes() != nullptr) {
          m->Attributes(mod->Attributes());
          for (auto a : *m->Attributes()) {
            a->VpiParent(m);
          }
        }
        uhdm_interfaces->push_back(m);
        writeInterface(mod, m, s, modPortMap);
      }
    }
    d->AllInterfaces(uhdm_interfaces);

    // Modules
    VectorOfmodule_inst* uhdm_modules = s.MakeModule_instVec();
    // Udps
    VectorOfudp_defn* uhdm_udps = s.MakeUdp_defnVec();
    for (const auto& modNamePair : modules) {
      ModuleDefinition* mod = modNamePair.second;
      if (mod->getFileContents().empty()) {
        // Built-in primitive
      } else if (mod->getType() == VObjectType::paModule_declaration) {
        const FileContent* fC = mod->getFileContents()[0];
        module_inst* m = s.MakeModule_inst();
        if (m_compileDesign->getCompiler()->isLibraryFile(
                mod->getFileContents()[0]->getFileId())) {
          m->VpiCellInstance(true);
          // Don't list library cells unused in the design
          if (mod && (designComponents.find(mod) == designComponents.end()))
            continue;
        }
        m_componentMap.emplace(mod, m);
        std::string_view modName = mod->getName();
        moduleMap.emplace(modName, m);
        m->VpiDefName(modName);
        if (modName.find("::") == std::string_view::npos) {
          m->VpiParent(d);
        } else {
          modName = StringUtils::rtrim_until(modName, ':');
          modName.remove_suffix(1);
          ModuleMap::const_iterator pmodIt = moduleMap.find(modName);
          if (pmodIt == moduleMap.end()) {
            m->VpiParent(d);
          } else {
            m->VpiParent(pmodIt->second);
          }
        }
        if (mod->Attributes() != nullptr) {
          m->Attributes(mod->Attributes());
          for (auto a : *m->Attributes()) {
            a->VpiParent(m);
          }
        }
        const NodeId modId = mod->getNodeIds()[0];
        const NodeId startId =
            fC->sl_collect(modId, VObjectType::paModule_keyword);
        fC->populateCoreMembers(startId, modId, m);
        uhdm_modules->push_back(m);
        writeModule(mod, m, s, moduleMap, modPortMap);
      } else if (mod->getType() == VObjectType::paUdp_declaration) {
        const FileContent* fC = mod->getFileContents()[0];
        UHDM::udp_defn* defn = mod->getUdpDefn();
        if (defn) {
          m_componentMap.emplace(mod, defn);
          defn->VpiParent(d);
          defn->VpiDefName(mod->getName());
          const NodeId modId = mod->getNodeIds()[0];
          const NodeId startId =
              fC->sl_collect(modId, VObjectType::paPRIMITIVE);
          fC->populateCoreMembers(startId, modId, defn);
          if (mod->Attributes() != nullptr) {
            defn->Attributes(mod->Attributes());
            for (auto a : *defn->Attributes()) {
              a->VpiParent(defn);
            }
          }
          uhdm_udps->push_back(defn);
        }
      }
    }
    d->AllModules(uhdm_modules);
    d->AllUdps(uhdm_udps);
    for (module_inst* mod : *uhdm_modules) {
      if (mod->Ref_modules()) {
        for (auto subMod : *mod->Ref_modules()) {
          ModuleMap::iterator itr =
              moduleMap.find(std::string(subMod->VpiDefName()));
          if (itr != moduleMap.end()) {
            subMod->Actual_group((*itr).second);
          }
        }
      }
    }

    // Classes
    auto classes = m_design->getClassDefinitions();
    VectorOfclass_defn* v4 = s.MakeClass_defnVec();
    for (const auto& classNamePair : classes) {
      ClassDefinition* classDef = classNamePair.second;
      if (!classDef->getFileContents().empty() &&
          classDef->getType() == VObjectType::paClass_declaration) {
        class_defn* c = classDef->getUhdmDefinition();
        if (!c->VpiParent()) {
          writeClass(classDef, v4, s, d);
        }
      }
    }
    d->AllClasses(v4);

    // -------------------------------
    // Elaborated Model (Folded)

    m_helper.setElabMode(true);

    // Top-level modules
    VectorOfmodule_inst* uhdm_top_modules = s.MakeModule_instVec();
    for (ModuleInstance* inst : topLevelModules) {
      DesignComponent* component = inst->getDefinition();
      ModuleDefinition* mod =
          valuedcomponenti_cast<ModuleDefinition*>(component);
      const auto& itr = m_componentMap.find(mod);
      module_inst* m = s.MakeModule_inst();
      m->VpiTopModule(true);
      m->VpiTop(true);
      module_inst* def = (module_inst*)itr->second;
      m->VpiDefName(def->VpiDefName());
      m->VpiName(def->VpiDefName());  // Top's instance name is module name
      m->VpiFullName(
          def->VpiDefName());  // Top's full instance name is module name
      m->VpiFile(def->VpiFile());
      m->VpiLineNo(def->VpiLineNo());
      m->VpiColumnNo(def->VpiColumnNo());
      m->VpiEndLineNo(def->VpiEndLineNo());
      m->VpiEndColumnNo(def->VpiEndColumnNo());
      writeInstance(mod, inst, m, m_compileDesign, modPortMap, instanceMap,
                    exprBuilder);
      uhdm_top_modules->push_back(m);
      m->VpiParent(d);
    }
    d->TopModules(uhdm_top_modules);
  }

  if (m_compileDesign->getCompiler()->getCommandLineParser()->getUhdmStats()) {
    s.PrintStats(std::cerr, "Non-Elaborated Model");
  }

  m_helper.setElabMode(true);

  // ----------------------------------
  // Fully elaborated model
  if (m_compileDesign->getCompiler()->getCommandLineParser()->getElabUhdm()) {
    Error err(ErrorDefinition::UHDM_ELABORATION, loc);
    m_compileDesign->getCompiler()->getErrorContainer()->addError(err);
    m_compileDesign->getCompiler()->getErrorContainer()->printMessages(
        m_compileDesign->getCompiler()->getCommandLineParser()->muteStdout());

    if (ElaboratorContext* elaboratorContext =
            new ElaboratorContext(&s, false, false)) {
      elaboratorContext->m_elaborator.uniquifyTypespec(false);
      elaboratorContext->m_elaborator.listenDesigns(designs);
      delete elaboratorContext;
    }

    if (m_compileDesign->getCompiler()
            ->getCommandLineParser()
            ->getUhdmStats()) {
      s.PrintStats(std::cerr, "Elaborated Model");
    }

    if (UhdmAdjuster* adjuster = new UhdmAdjuster(&s, d)) {
      adjuster->listenDesigns(designs);
      delete adjuster;
    }
  }

  // ----------------------------------
  // Lint only the elaborated model
  if (UhdmLint* linter = new UhdmLint(&s, d)) {
    linter->listenDesigns(designs);
    delete linter;
  }

  if (m_compileDesign->getCompiler()
          ->getCommandLineParser()
          ->reportNonSynthesizable()) {
    std::set<const any*> nonSynthesizableObjects;
    if (SynthSubset* annotate =
            new SynthSubset(&s, nonSynthesizableObjects, d, true,
                            m_compileDesign->getCompiler()
                                ->getCommandLineParser()
                                ->reportNonSynthesizableWithFormal())) {
      annotate->listenDesigns(designs);
      annotate->filterNonSynthesizable();
      delete annotate;
    }
  }

  // Purge obsolete typespecs
  for (auto o : m_compileDesign->getSwapedObjects()) {
    const typespec* orig = o.first;
    const typespec* tps = o.second;
    if (tps != orig) s.Erase(orig);
  }

  const fs::path uhdmFile = fileSystem->toPlatformAbsPath(uhdmFileId);
  if (m_compileDesign->getCompiler()->getCommandLineParser()->writeUhdm()) {
    Error err(ErrorDefinition::UHDM_WRITE_DB, loc);
    m_compileDesign->getCompiler()->getErrorContainer()->addError(err);
    m_compileDesign->getCompiler()->getErrorContainer()->printMessages(
        m_compileDesign->getCompiler()->getCommandLineParser()->muteStdout());
    s.SetGCEnabled(
        m_compileDesign->getCompiler()->getCommandLineParser()->gc());
    s.Save(uhdmFile);
  }

  if (m_compileDesign->getCompiler()->getCommandLineParser()->getDebugUhdm() ||
      m_compileDesign->getCompiler()->getCommandLineParser()->getCoverUhdm()) {
    // Check before restore
    Location loc(fileSystem->getCheckerHtmlFile(
        uhdmFileId, m_compileDesign->getCompiler()->getSymbolTable()));
    Error err(ErrorDefinition::UHDM_WRITE_HTML_COVERAGE, loc);
    m_compileDesign->getCompiler()->getErrorContainer()->addError(err);
    m_compileDesign->getCompiler()->getErrorContainer()->printMessages(
        m_compileDesign->getCompiler()->getCommandLineParser()->muteStdout());

    if (UhdmChecker* uhdmchecker = new UhdmChecker(m_compileDesign, m_design)) {
      uhdmchecker->check(uhdmFileId);
      delete uhdmchecker;
    }
  }

  if (m_compileDesign->getCompiler()->getCommandLineParser()->getDebugUhdm()) {
    if (m_compileDesign->getCompiler()->getCommandLineParser()->writeUhdm()) {
      Location loc((SymbolId)uhdmFileId);
      Error err1(ErrorDefinition::UHDM_LOAD_DB, loc);
      m_compileDesign->getCompiler()->getErrorContainer()->addError(err1);
      m_compileDesign->getCompiler()->getErrorContainer()->printMessages(
          m_compileDesign->getCompiler()->getCommandLineParser()->muteStdout());
      const std::vector<vpiHandle>& restoredDesigns =
          s.Restore(uhdmFile.string());

      Error err2(ErrorDefinition::UHDM_VISITOR, loc);
      m_compileDesign->getCompiler()->getErrorContainer()->addError(err2);
      m_compileDesign->getCompiler()->getErrorContainer()->printMessages(
          m_compileDesign->getCompiler()->getCommandLineParser()->muteStdout());

      std::cout << "====== UHDM =======\n";
      if (!restoredDesigns.empty()) {
        designHandle = restoredDesigns[0];
      }
      vpi_show_ids(
          m_compileDesign->getCompiler()->getCommandLineParser()->showVpiIds());
      visit_designs(restoredDesigns, std::cout);
      std::cout << "===================\n";
    } else {
      Location loc(
          m_compileDesign->getCompiler()->getSymbolTable()->registerSymbol(
              "in-memory uhdm"));
      Error err2(ErrorDefinition::UHDM_VISITOR, loc);
      m_compileDesign->getCompiler()->getErrorContainer()->addError(err2);
      m_compileDesign->getCompiler()->getErrorContainer()->printMessages(
          m_compileDesign->getCompiler()->getCommandLineParser()->muteStdout());
      std::cout << "====== UHDM =======\n";
      vpi_show_ids(
          m_compileDesign->getCompiler()->getCommandLineParser()->showVpiIds());
      visit_designs({designHandle}, std::cout);
      std::cout << "===================\n";
    }
  }
  m_compileDesign->getCompiler()->getErrorContainer()->printMessages(
      m_compileDesign->getCompiler()->getCommandLineParser()->muteStdout());
  return designHandle;
}
}  // namespace SURELOG
