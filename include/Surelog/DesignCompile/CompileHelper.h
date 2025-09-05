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
 * File:   CompileHelper.h
 * Author: alain
 *
 * Created on May 14, 2019, 8:03 PM
 */

#ifndef SURELOG_COMPILEHELPER_H
#define SURELOG_COMPILEHELPER_H
#pragma once

#include <Surelog/Common/PathId.h>
#include <Surelog/Common/RTTI.h>
#include <Surelog/Design/ModuleDefinition.h>
#include <Surelog/Design/ValuedComponentI.h>
#include <Surelog/Expression/ExprBuilder.h>
#include <Surelog/SourceCompile/VObjectTypes.h>

#include <cstdint>
#include <string>
#include <string_view>
#include <unordered_map>
#include <utility>
#include <vector>

// UHDM
#include <uhdm/always.h>
#include <uhdm/array_var.h>
#include <uhdm/assignment.h>
#include <uhdm/atomic_stmt.h>
#include <uhdm/attribute.h>
#include <uhdm/clocking_block.h>
#include <uhdm/constant.h>
#include <uhdm/cont_assign.h>
#include <uhdm/containers.h>
#include <uhdm/event_control.h>
#include <uhdm/expr.h>
#include <uhdm/final_stmt.h>
#include <uhdm/function.h>
#include <uhdm/hier_path.h>
#include <uhdm/initial.h>
#include <uhdm/int_typespec.h>
#include <uhdm/io_decl.h>
#include <uhdm/method_func_call.h>
#include <uhdm/module_array.h>
#include <uhdm/module_inst.h>
#include <uhdm/primitive.h>
#include <uhdm/property_decl.h>
#include <uhdm/range.h>
#include <uhdm/ref_module.h>
#include <uhdm/sequence_decl.h>
#include <uhdm/task_func.h>
#include <uhdm/typespec.h>
#include <uhdm/typespec_member.h>
#include <uhdm/uhdm_types.h>
#include <uhdm/variables.h>

namespace SURELOG {

class CompileDesign;
class DataType;
class Design;
class DesignComponent;
class ErrorContainer;
class FileContent;
class Function;
class NodeId;
class Procedure;
class Scope;
class Statement;
class SymbolTable;
class Task;
class TfPortItem;
using TfPortList = std::vector<TfPortItem*>;

class FScope : public ValuedComponentI {
  SURELOG_IMPLEMENT_RTTI(FScope, ValuedComponentI)
 public:
  FScope(const SURELOG::ValuedComponentI* parent,
         SURELOG::ValuedComponentI* definition)
      : ValuedComponentI(parent, definition) {}

 private:
};

using Scopes = std::vector<FScope*>;
enum class Reduce : bool { Yes = true, No = false };

class CompileHelper final {
 public:
  CompileHelper() = default;
  CompileHelper(const CompileHelper&) = delete;

  void seterrorReporting(ErrorContainer* errors, SymbolTable* symbols) {
    m_errors = errors;
    m_symbols = symbols;
    m_exprBuilder.seterrorReporting(errors, symbols);
  }

  void setDesign(Design* design) { m_exprBuilder.setDesign(design); }

  // ------------------------------------------------------------------------------------------
  // Surelog internal modeling

  bool importPackage(DesignComponent* scope, Design* design,
                     const FileContent* fC, NodeId id,
                     CompileDesign* compileDesign, bool inPackage = false);

  bool compileTfPortList(Procedure* parent, const FileContent* fC, NodeId id,
                         TfPortList& targetList);

  const DataType* compileTypeDef(DesignComponent* scope, const FileContent* fC,
                                 NodeId id, CompileDesign* compileDesign,
                                 Reduce reduce, UHDM::any* pstmt = nullptr);

  bool compileScopeBody(Scope* parent, Statement* parentStmt,
                        const FileContent* fC, NodeId id);

  bool compileScopeVariable(Scope* parent, const FileContent* fC, NodeId id);

  bool compileSubroutine_call(Scope* parent, Statement* parentStmt,
                              const FileContent* fC, NodeId id);

  bool compileSeqBlock_stmt(Scope* parent, Statement* parentStmt,
                            const FileContent* fC, NodeId id);

  bool compileLoop_stmt(Scope* parent, Statement* parentStmt,
                        const FileContent* fC, NodeId id);

  bool compileForLoop_stmt(Scope* parent, Statement* parentStmt,
                           const FileContent* fC, NodeId id);

  bool compileForeachLoop_stmt(Scope* parent, Statement* parentStmt,
                               const FileContent* fC, NodeId id);

  Function* compileFunctionPrototype(DesignComponent* scope,
                                     const FileContent* fC, NodeId id,
                                     CompileDesign* compileDesign);

  Task* compileTaskPrototype(DesignComponent* scope, const FileContent* fC,
                             NodeId id, CompileDesign* compileDesign);

  bool compilePortDeclaration(DesignComponent* scope, const FileContent* fC,
                              NodeId id, CompileDesign* compileDesign,
                              VObjectType& port_direction, bool hasNonNullPort);

  bool compileAnsiPortDeclaration(DesignComponent* component,
                                  const FileContent* fC, NodeId id,
                                  VObjectType& port_direction);

  bool elaborationSystemTask(DesignComponent* component, const FileContent* fC,
                             NodeId id, CompileDesign* compileDesign);

  bool compileNetDeclaration(DesignComponent* component, const FileContent* fC,
                             NodeId id, bool interface,
                             CompileDesign* compileDesign,
                             UHDM::VectorOfattribute* attributes);

  bool compileDataDeclaration(DesignComponent* component, const FileContent* fC,
                              NodeId id, bool interface,
                              CompileDesign* compileDesign, Reduce reduce,
                              UHDM::VectorOfattribute* attributes);

  // ------------------------------------------------------------------------------------------
  // UHDM modeling

  std::vector<UHDM::cont_assign*> compileContinuousAssignment(
      DesignComponent* component, const FileContent* fC, NodeId id,
      CompileDesign* compileDesign, ValuedComponentI* instance);

  UHDM::always* compileAlwaysBlock(DesignComponent* component,
                                   const FileContent* fC, NodeId id,
                                   CompileDesign* compileDesign,
                                   ValuedComponentI* instance);

  UHDM::any* compileTfCall(DesignComponent* component, const FileContent* fC,
                           NodeId Tf_call_stmt, CompileDesign* compileDesign,
                           UHDM::any* pexpr);

  UHDM::VectorOfany* compileTfCallArguments(
      DesignComponent* component, const FileContent* fC, NodeId Arg_list_node,
      CompileDesign* compileDesign, Reduce reduce, UHDM::any* call,
      ValuedComponentI* instance, bool muteErrors);

  UHDM::assignment* compileBlockingAssignment(
      DesignComponent* component, const FileContent* fC, NodeId nodeId,
      bool blocking, CompileDesign* compileDesign, UHDM::any* pstmt,
      ValuedComponentI* instance = nullptr);

  UHDM::atomic_stmt* compileProceduralTimingControlStmt(
      DesignComponent* component, const FileContent* fC, NodeId nodeId,
      CompileDesign* compileDesign, UHDM::any* pstmt,
      ValuedComponentI* instance = nullptr);

  UHDM::atomic_stmt* compileEventControlStmt(
      DesignComponent* component, const FileContent* fC, NodeId nodeId,
      CompileDesign* compileDesign, UHDM::any* pstmt,
      ValuedComponentI* instance = nullptr, bool muteErrors = false);

  UHDM::atomic_stmt* compileConditionalStmt(
      DesignComponent* component, const FileContent* fC, NodeId nodeId,
      CompileDesign* compileDesign, UHDM::any* pstmt,
      ValuedComponentI* instance = nullptr, bool muteErrors = false);

  bool compileParameterDeclaration(DesignComponent* component,
                                   const FileContent* fC, NodeId nodeId,
                                   CompileDesign* compileDesign, Reduce reduce,
                                   bool localParam,
                                   ValuedComponentI* m_instance,
                                   bool port_param, bool muteErrors);

  NodeId setFuncTaskQualifiers(const FileContent* fC, NodeId nodeId,
                               UHDM::task_func* func);

  bool compileTask(DesignComponent* component, const FileContent* fC,
                   NodeId nodeId, CompileDesign* compileDesign, Reduce reduce,
                   ValuedComponentI* instance, bool isMethod);

  bool compileFunction(DesignComponent* component, const FileContent* fC,
                       NodeId nodeId, CompileDesign* compileDesign,
                       Reduce reduce, ValuedComponentI* instance,
                       bool isMethod);

  bool compileAssertionItem(DesignComponent* component, const FileContent* fC,
                            NodeId nodeId, CompileDesign* compileDesign);

  std::vector<UHDM::io_decl*>* compileTfPortList(DesignComponent* scope,
                                                 UHDM::task_func* parent,
                                                 const FileContent* fC,
                                                 NodeId id,
                                                 CompileDesign* compileDesign);

  std::pair<std::vector<UHDM::io_decl*>*, std::vector<UHDM::variables*>*>
  compileTfPortDecl(DesignComponent* scope, UHDM::task_func* parent,
                    const FileContent* fC, NodeId id,
                    CompileDesign* compileDesign);

  UHDM::atomic_stmt* compileCaseStmt(DesignComponent* component,
                                     const FileContent* fC, NodeId nodeId,
                                     CompileDesign* compileDesign,
                                     UHDM::any* pstmt = nullptr,
                                     ValuedComponentI* instance = nullptr,
                                     bool muteErrors = false);
  UHDM::atomic_stmt* compileRandcaseStmt(DesignComponent* component,
                                         const FileContent* fC, NodeId nodeId,
                                         CompileDesign* compileDesign,
                                         UHDM::any* pstmt = nullptr,
                                         ValuedComponentI* instance = nullptr,
                                         bool muteErrors = false);

  UHDM::VectorOfany* compileStmt(DesignComponent* component,
                                 const FileContent* fC, NodeId nodeId,
                                 CompileDesign* compileDesign, Reduce reduce,
                                 UHDM::any* pstmt = nullptr,
                                 ValuedComponentI* instance = nullptr,
                                 bool muteError = false);

  UHDM::any* compileVariable(DesignComponent* component, const FileContent* fC,
                             NodeId nodeId, CompileDesign* compileDesign,
                             Reduce reduce, UHDM::any* pstmt,
                             ValuedComponentI* instance, bool muteErrors,
                             bool implicitInt = false);

  UHDM::typespec* compileTypespec(DesignComponent* component,
                                  const FileContent* fC, NodeId nodeId,
                                  CompileDesign* compileDesign, Reduce reduce,
                                  UHDM::any* pstmt, ValuedComponentI* instance,
                                  bool isVariable);

  UHDM::typespec* compileBuiltinTypespec(DesignComponent* component,
                                         const FileContent* fC, NodeId type,
                                         VObjectType the_type,
                                         CompileDesign* compileDesign,
                                         std::vector<UHDM::range*>* ranges);

  UHDM::typespec* compileDatastructureTypespec(
      DesignComponent* component, const FileContent* fC, NodeId type,
      CompileDesign* compileDesign, Reduce reduce,
      SURELOG::ValuedComponentI* instance, std::string_view suffixname = "",
      std::string_view typeName = "");

  UHDM::any* compileCheckerInstantiation(DesignComponent* component,
                                         const FileContent* fC, NodeId nodeId,
                                         CompileDesign* compileDesign,
                                         UHDM::any* pstmt,
                                         ValuedComponentI* instance);

  UHDM::any* compileSimpleImmediateAssertion(DesignComponent* component,
                                             const FileContent* fC,
                                             NodeId nodeId,
                                             CompileDesign* compileDesign,
                                             UHDM::any* pstmt,
                                             ValuedComponentI* instance);

  UHDM::any* compileDeferredImmediateAssertion(DesignComponent* component,
                                               const FileContent* fC,
                                               NodeId nodeId,
                                               CompileDesign* compileDesign,
                                               UHDM::any* pstmt,
                                               ValuedComponentI* instance);

  UHDM::any* compileConcurrentAssertion(DesignComponent* component,
                                        const FileContent* fC, NodeId nodeId,
                                        CompileDesign* compileDesign,
                                        UHDM::any* pstmt,
                                        ValuedComponentI* instance);

  UHDM::property_decl* compilePropertyDeclaration(DesignComponent* component,
                                                  const FileContent* fC,
                                                  NodeId nodeId,
                                                  CompileDesign* compileDesign,
                                                  UHDM::any* pstmt,
                                                  ValuedComponentI* instance);

  UHDM::sequence_decl* compileSequenceDeclaration(DesignComponent* component,
                                                  const FileContent* fC,
                                                  NodeId nodeId,
                                                  CompileDesign* compileDesign,
                                                  UHDM::any* pstmt,
                                                  ValuedComponentI* instance);

  UHDM::initial* compileInitialBlock(DesignComponent* component,
                                     const FileContent* fC, NodeId id,
                                     CompileDesign* compileDesign);

  UHDM::final_stmt* compileFinalBlock(DesignComponent* component,
                                      const FileContent* fC, NodeId id,
                                      CompileDesign* compileDesign);

  void compileBindStmt(DesignComponent* component, const FileContent* fC,
                       NodeId nodeId, CompileDesign* compileDesign,
                       ValuedComponentI* instance = nullptr);

  UHDM::constant* constantFromValue(Value* val, CompileDesign* compileDesign);

  UHDM::any* compileExpression(DesignComponent* component,
                               const FileContent* fC, NodeId nodeId,
                               CompileDesign* compileDesign, Reduce reduce,
                               UHDM::any* pexpr = nullptr,
                               ValuedComponentI* instance = nullptr,
                               bool muteErrors = false);

  UHDM::any* compilePartSelectRange(
      DesignComponent* component, const FileContent* fC, NodeId Constant_range,
      std::string_view name, CompileDesign* compileDesign, Reduce reduce,
      UHDM::any* pexpr, ValuedComponentI* instance, bool muteErrors);

  std::vector<UHDM::range*>* compileRanges(DesignComponent* component,
                                           const FileContent* fC,
                                           NodeId Packed_dimension,
                                           CompileDesign* compileDesign,
                                           Reduce reduce, UHDM::any* pexpr,
                                           ValuedComponentI* instance,
                                           int32_t& size, bool muteErrors);

  UHDM::any* compileAssignmentPattern(DesignComponent* component,
                                      const FileContent* fC,
                                      NodeId Assignment_pattern,
                                      CompileDesign* compileDesign,
                                      Reduce reduce, UHDM::any* pexpr,
                                      ValuedComponentI* instance);

  UHDM::array_var* compileArrayVar(DesignComponent* component,
                                   const FileContent* fC, NodeId varId,
                                   CompileDesign* compileDesign,
                                   UHDM::any* pexpr,
                                   ValuedComponentI* instance);

  UHDM::any* compileProceduralContinuousAssign(DesignComponent* component,
                                               const FileContent* fC,
                                               NodeId nodeId,
                                               CompileDesign* compileDesign);

  UHDM::VectorOfany* compileDataDeclaration(
      DesignComponent* component, const FileContent* fC, NodeId nodeId,
      CompileDesign* compileDesign, Reduce reduce, UHDM::any* pstmt = nullptr,
      ValuedComponentI* instance = nullptr);

  UHDM::any* compileForLoop(DesignComponent* component, const FileContent* fC,
                            NodeId nodeId, CompileDesign* compileDesign,
                            bool muteErrors = false);

  UHDM::any* compileSelectExpression(
      DesignComponent* component, const FileContent* fC, NodeId Bit_select,
      std::string_view name, CompileDesign* compileDesign, Reduce reduce,
      UHDM::any* pexpr, ValuedComponentI* instance, bool muteErrors);

  UHDM::any* compileBits(DesignComponent* component, const FileContent* fC,
                         NodeId Expression, CompileDesign* compileDesign,
                         Reduce reduce, UHDM::any* pexpr,
                         ValuedComponentI* instance, bool sizeMode,
                         bool muteErrors);

  UHDM::any* compileClog2(DesignComponent* component, const FileContent* fC,
                          NodeId Expression, CompileDesign* compileDesign,
                          Reduce reduce, UHDM::any* pexpr,
                          ValuedComponentI* instance, bool muteErrors);

  UHDM::any* compileBound(DesignComponent* component, const FileContent* fC,
                          NodeId Expression, CompileDesign* compileDesign,
                          Reduce reduce, UHDM::any* pexpr,
                          ValuedComponentI* instance, bool muteErrors,
                          std::string_view name);

  UHDM::any* compileTypename(DesignComponent* component, const FileContent* fC,
                             NodeId Expression, CompileDesign* compileDesign,
                             Reduce reduce, UHDM::any* pexpr,
                             ValuedComponentI* instance);

  const UHDM::typespec* getTypespec(DesignComponent* component,
                                    const FileContent* fC, NodeId id,
                                    CompileDesign* compileDesign, Reduce reduce,
                                    ValuedComponentI* instance);

  UHDM::any* compileComplexFuncCall(DesignComponent* component,
                                    const FileContent* fC, NodeId nodeId,
                                    CompileDesign* compileDesign, Reduce reduce,
                                    UHDM::any* pexpr,
                                    ValuedComponentI* instance,
                                    bool muteErrors);

  std::vector<UHDM::attribute*>* compileAttributes(DesignComponent* component,
                                                   const FileContent* fC,
                                                   NodeId nodeId,
                                                   CompileDesign* compileDesign,
                                                   UHDM::any* pexpr);

  void compileImportDeclaration(DesignComponent* component,
                                const FileContent* fC, NodeId id,
                                CompileDesign* compileDesign);

  UHDM::any* bindVariable(DesignComponent* component, const UHDM::any* scope,
                          std::string_view name, CompileDesign* compileDesign);

  UHDM::any* bindVariable(DesignComponent* component,
                          ValuedComponentI* instance, std::string_view name,
                          CompileDesign* compileDesign);

  UHDM::any* bindParameter(DesignComponent* component,
                           ValuedComponentI* instance, std::string_view name,
                           CompileDesign* compileDesign, bool crossHierarchy);

  UHDM::event_control* compileClocking_event(DesignComponent* component,
                                             const FileContent* fC,
                                             NodeId nodeId,
                                             CompileDesign* compileDesign,
                                             UHDM::any* pexpr,
                                             ValuedComponentI* instance);

  UHDM::clocking_block* compileClockingBlock(DesignComponent* component,
                                             const FileContent* fC,
                                             NodeId nodeId,
                                             CompileDesign* compileDesign,
                                             UHDM::any* pexpr,
                                             ValuedComponentI* instance);

  UHDM::atomic_stmt* compileDelayControl(DesignComponent* component,
                                         const FileContent* fC,
                                         NodeId Procedural_timing_control,
                                         CompileDesign* compileDesign,
                                         UHDM::any* pexpr,
                                         ValuedComponentI* instance);

  bool compileClassConstructorDeclaration(DesignComponent* component,
                                          const FileContent* fC, NodeId nodeId,
                                          CompileDesign* compileDesign);

  UHDM::method_func_call* compileRandomizeCall(DesignComponent* component,
                                               const FileContent* fC,
                                               NodeId nodeId,
                                               CompileDesign* compileDesign,
                                               UHDM::any* pexpr);

  UHDM::any* compileConstraintBlock(DesignComponent* component,
                                    const FileContent* fC, NodeId nodeId,
                                    CompileDesign* compileDesign,
                                    UHDM::any* pexpr);

  uint32_t getBuiltinType(VObjectType type);

  void compileLetDeclaration(DesignComponent* component, const FileContent* fC,
                             NodeId nodeId, CompileDesign* compileDesign);

  std::pair<std::vector<UHDM::module_array*>, std::vector<UHDM::ref_module*>>
  compileInstantiation(ModuleDefinition* mod, const FileContent* fC,
                       CompileDesign* compileDesign, NodeId id,
                       ValuedComponentI* instance);

  void writePrimTerms(ModuleDefinition* mod, const FileContent* fC,
                      CompileDesign* compileDesign, NodeId id,
                      UHDM::primitive* prim, int32_t vpiGateType,
                      ValuedComponentI* instance);

  void compileUdpInstantiation(ModuleDefinition* mod, const FileContent* fC,
                               CompileDesign* compileDesign, NodeId id,
                               ValuedComponentI* instance);

  void compileGateInstantiation(ModuleDefinition* mod, const FileContent* fC,
                                CompileDesign* compileDesign, NodeId id,
                                ValuedComponentI* instance);

  void compileHighConn(ModuleDefinition* component, const FileContent* fC,
                       CompileDesign* compileDesign, NodeId id,
                       UHDM::VectorOfport* ports);

  UHDM::VectorOfgen_stmt* compileGenStmt(ModuleDefinition* component,
                                         const FileContent* fC,
                                         CompileDesign* compileDesign,
                                         NodeId id);

  /** Variable is either a bit select or a range */
  bool isSelected(const FileContent* fC, NodeId id);

  void setParentNoOverride(UHDM::any* obj, UHDM::any* parent);

  bool isMultidimensional(UHDM::typespec* ts, DesignComponent* component);

  bool isDecreasingRange(UHDM::typespec* ts, DesignComponent* component);

  UHDM::expr* reduceExpr(UHDM::any* expr, bool& invalidValue,
                         DesignComponent* component,
                         CompileDesign* compileDesign,
                         ValuedComponentI* instance, PathId fileId,
                         uint32_t lineNumber, UHDM::any* pexpr,
                         bool muteErrors = false);

  int32_t adjustOpSize(const UHDM::typespec* tps, UHDM::expr* cop,
                       int32_t opIndex, UHDM::expr* rhs,
                       DesignComponent* component, CompileDesign* compileDesign,
                       ValuedComponentI* instance);

  void adjustUnsized(UHDM::constant* c, int32_t size);

  UHDM::any* defaultPatternAssignment(const UHDM::typespec* tps, UHDM::any* exp,
                                      DesignComponent* component,
                                      CompileDesign* compileDesign,
                                      ValuedComponentI* instance);

  UHDM::expr* expandPatternAssignment(const UHDM::typespec* tps,
                                      UHDM::expr* rhs,
                                      DesignComponent* component,
                                      CompileDesign* compileDesign,
                                      ValuedComponentI* instance);

  uint64_t Bits(const UHDM::any* typespec, bool& invalidValue,
                DesignComponent* component, CompileDesign* compileDesign,
                Reduce reduce, ValuedComponentI* instance, PathId fileId,
                uint32_t lineNumber, bool sizeMode);

  UHDM::variables* getSimpleVarFromTypespec(
      UHDM::typespec* spec, std::vector<UHDM::range*>* packedDimensions,
      CompileDesign* compileDesign);

  std::pair<UHDM::task_func*, DesignComponent*> getTaskFunc(
      std::string_view name, DesignComponent* component,
      CompileDesign* compileDesign, ValuedComponentI* instance,
      UHDM::any* pexpr);

  UHDM::expr* EvalFunc(UHDM::function* func, std::vector<UHDM::any*>* args,
                       bool& invalidValue, DesignComponent* component,
                       CompileDesign* compileDesign, ValuedComponentI* instance,
                       PathId fileId, uint32_t lineNumber, UHDM::any* pexpr);

  void evalScheduledExprs(DesignComponent* component,
                          CompileDesign* compileDesign);

  void checkForLoops(bool on);
  bool loopDetected(PathId fileId, uint32_t lineNumber,
                    CompileDesign* compileDesign, ValuedComponentI* instance);

  UHDM::any* getValue(std::string_view name, DesignComponent* component,
                      CompileDesign* compileDesign, Reduce reduce,
                      ValuedComponentI* instance, PathId fileId,
                      uint32_t lineNumber, UHDM::any* pexpr,
                      bool muteErrors = false);

  // Parse numeric UHDM constant into int64_t. Returns if successful.
  bool parseConstant(const UHDM::constant& constant, int64_t* value);

  int64_t getValue(bool& validValue, DesignComponent* component,
                   const FileContent* fC, NodeId nodeId,
                   CompileDesign* compileDesign, Reduce reduce,
                   UHDM::any* pexpr, ValuedComponentI* instance,
                   bool muteErrors = false);

  UHDM::typespec* elabTypespec(DesignComponent* component, UHDM::typespec* spec,
                               CompileDesign* compileDesign,
                               UHDM::any* pexpr = nullptr,
                               ValuedComponentI* instance = nullptr);

  bool substituteAssignedValue(const UHDM::any* op,
                               CompileDesign* compileDesign);

  UHDM::any* getObject(std::string_view name, DesignComponent* component,
                       CompileDesign* compileDesign, ValuedComponentI* instance,
                       const UHDM::any* pexpr);

  void reorderAssignmentPattern(DesignComponent* mod, const UHDM::any* lhs,
                                UHDM::any* rhs, CompileDesign* compileDesign,
                                ValuedComponentI* instance, uint32_t level);

  bool errorOnNegativeConstant(DesignComponent* component, UHDM::expr* exp,
                               CompileDesign* compileDesign,
                               ValuedComponentI* instance);
  bool errorOnNegativeConstant(DesignComponent* component, Value* value,
                               CompileDesign* compileDesign,
                               ValuedComponentI* instance);
  bool errorOnNegativeConstant(DesignComponent* component,
                               std::string_view value,
                               CompileDesign* compileDesign,
                               ValuedComponentI* instance, PathId fileId,
                               uint32_t lineNo, uint16_t columnNo);

  UHDM::any* decodeHierPath(UHDM::hier_path* path, bool& invalidValue,
                            DesignComponent* component,
                            CompileDesign* compileDesign, Reduce reduce,
                            ValuedComponentI* instance, PathId fileName,
                            uint32_t lineNumber, UHDM::any* pexpr,
                            bool muteErrors, bool returnTypespec);

  bool valueRange(Value* val, const UHDM::typespec* lhstps,
                  const UHDM::typespec* rhstps, DesignComponent* component,
                  CompileDesign* compileDesign, ValuedComponentI* instance);

  void setRange(UHDM::constant* c, Value* val, CompileDesign* compileDesign);

  UHDM::constant* adjustSize(const UHDM::typespec* ts,
                             DesignComponent* component,
                             CompileDesign* compileDesign,
                             ValuedComponentI* instance, UHDM::constant* c,
                             bool uniquify = false, bool sizeMode = false);

  /** task/func/scope */
  UHDM::any* searchObjectName(std::string_view name, DesignComponent* component,
                              CompileDesign* compileDesign, UHDM::any* stmt);

  bool isOverloaded(const UHDM::any* expr, CompileDesign* compileDesign,
                    ValuedComponentI* instance);

  std::string decompileHelper(const UHDM::any* sel);

  void setElabMode(bool on) { m_elabMode = on; }

 private:
  ErrorContainer* m_errors = nullptr;
  SymbolTable* m_symbols = nullptr;
  ExprBuilder m_exprBuilder;
  UHDM::module_inst* m_exprEvalPlaceHolder = nullptr;
  // Caches
  UHDM::int_typespec* buildIntTypespec(CompileDesign* compileDesign,
                                       PathId fileId, std::string_view name,
                                       std::string_view value, uint32_t line,
                                       uint16_t column, uint32_t eline,
                                       uint16_t ecolumn);
  UHDM::typespec_member* buildTypespecMember(CompileDesign* compileDesign,
                                             PathId fileId,
                                             std::string_view name,
                                             std::string_view value,
                                             uint32_t line, uint16_t column,
                                             uint32_t eline, uint16_t ecolumn);
  std::unordered_map<std::string, UHDM::int_typespec*> m_cache_int_typespec;
  std::unordered_map<std::string, UHDM::typespec_member*>
      m_cache_typespec_member;
  bool m_checkForLoops = false;
  int32_t m_stackLevel = 0;
  bool m_unwind = false;
  bool m_elabMode = true;
};

}  // namespace SURELOG

#endif /* SURELOG_COMPILEHELPER_H */
