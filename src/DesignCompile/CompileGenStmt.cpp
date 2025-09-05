/*
 Copyright 2019-2023 Alain Dargelas

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
 * File:   CompileGenStmt.cpp
 * Author: alain
 *
 * Created on May 14, 2023, 11:45 AM
 */

#include "Surelog/Design/DataType.h"
#include "Surelog/Design/DummyType.h"
#include "Surelog/Design/Enum.h"
#include "Surelog/Design/FileContent.h"
#include "Surelog/Design/ModuleDefinition.h"
#include "Surelog/Design/ModuleInstance.h"
#include "Surelog/Design/ParamAssign.h"
#include "Surelog/Design/Parameter.h"
#include "Surelog/Design/Signal.h"
#include "Surelog/Design/SimpleType.h"
#include "Surelog/Design/Struct.h"
#include "Surelog/DesignCompile/CompileDesign.h"
#include "Surelog/DesignCompile/CompileHelper.h"
#include "Surelog/DesignCompile/UhdmWriter.h"
#include "Surelog/Library/Library.h"
#include "Surelog/Package/Package.h"
#include "Surelog/SourceCompile/Compiler.h"
#include "Surelog/SourceCompile/VObjectTypes.h"
#include "Surelog/Testbench/ClassDefinition.h"
#include "Surelog/Testbench/Program.h"
#include "Surelog/Testbench/TypeDef.h"
#include "Surelog/Testbench/Variable.h"

// UHDM
#include <uhdm/ElaboratorListener.h>
#include <uhdm/ExprEval.h>
#include <uhdm/clone_tree.h>
#include <uhdm/expr.h>
#include <uhdm/uhdm.h>

#include <climits>

namespace SURELOG {

using namespace UHDM;  // NOLINT (we use a good chunk of these here)

UHDM::VectorOfgen_stmt* CompileHelper::compileGenStmt(
    ModuleDefinition* component, const FileContent* fC,
    CompileDesign* compileDesign, NodeId id) {
  Serializer& s = compileDesign->getSerializer();
  NodeId stmtId = fC->Child(id);
  gen_stmt* genstmt = nullptr;
  if (fC->Type(id) == VObjectType::paGenerate_region) {
    gen_region* genreg = s.MakeGen_region();
    genstmt = genreg;
    ModuleDefinition* subComponent =
        new ModuleDefinition(fC, id, "GENERATE_STMT_PLACEHOLDER");
    component = subComponent;
    checkForLoops(true);
    VectorOfany* stmts = compileStmt(component, fC, stmtId, compileDesign,
                                     Reduce::No, nullptr, nullptr, true);
    checkForLoops(false);
    NodeId blockNameId = fC->Child(fC->Child(stmtId));
    if (fC->Type(blockNameId) == VObjectType::slStringConst) {
      std::string_view blockName = fC->SymName(blockNameId);
      named_begin* stmt = s.MakeNamed_begin();
      stmt->VpiName(blockName);
      stmt->VpiParent(genreg);
      genreg->VpiStmt(stmt);
      if (stmts != nullptr) {
        stmt->Stmts(stmts);
        for (auto s : *stmts) s->VpiParent(stmt);
      }
    } else {
      begin* stmt = s.MakeBegin();
      stmt->VpiParent(genreg);
      genreg->VpiStmt(stmt);
      if (stmts != nullptr) {
        stmt->Stmts(stmts);
        for (auto s : *stmts) s->VpiParent(stmt);
      }
    }

  } else if (fC->Type(stmtId) ==
             VObjectType::paIf_generate_construct) {  // If, If-Else stmt
    NodeId ifElseId = fC->Child(stmtId);
    if (fC->Type(ifElseId) == VObjectType::paIF) {
      // lookahead
      NodeId tmp = ifElseId;
      bool ifelse = false;
      while (tmp) {
        if (fC->Type(tmp) == VObjectType::paELSE) {
          ifelse = true;
          break;
        }
        tmp = fC->Sibling(tmp);
      }

      NodeId condId = fC->Sibling(ifElseId);
      checkForLoops(true);
      expr* cond = (expr*)compileExpression(component, fC, condId,
                                            compileDesign, Reduce::No, nullptr);
      checkForLoops(false);
      NodeId stmtId = fC->Sibling(condId);
      if (ifelse) {
        gen_if_else* genif = s.MakeGen_if_else();
        genstmt = genif;
        if (cond != nullptr) {
          cond->VpiParent(genif);
          genif->VpiCondition(cond);
        }
        checkForLoops(true);
        ModuleDefinition* subComponent =
            new ModuleDefinition(fC, id, "GENERATE_STMT_PLACEHOLDER");
        component = subComponent;
        VectorOfany* stmts = compileStmt(component, fC, stmtId, compileDesign,
                                         Reduce::No, nullptr, nullptr, true);
        checkForLoops(false);
        NodeId blockNameId = fC->Child(fC->Child(stmtId));
        if (fC->Type(blockNameId) == VObjectType::slStringConst) {
          std::string_view blockName = fC->SymName(blockNameId);
          named_begin* stmt = s.MakeNamed_begin();
          stmt->VpiName(blockName);
          stmt->VpiParent(genif);
          genif->VpiStmt(stmt);
          if (stmts != nullptr) {
            stmt->Stmts(stmts);
            for (auto s : *stmts) s->VpiParent(stmt);
          }
        } else {
          begin* stmt = s.MakeBegin();
          stmt->VpiParent(genif);
          genif->VpiStmt(stmt);
          if (stmts != nullptr) {
            stmt->Stmts(stmts);
            for (auto s : *stmts) s->VpiParent(stmt);
          }
        }

        NodeId ElseId = fC->Sibling(stmtId);
        NodeId elseStmtId = fC->Sibling(ElseId);
        checkForLoops(true);
        subComponent =
            new ModuleDefinition(fC, id, "GENERATE_STMT_PLACEHOLDER");
        component = subComponent;
        stmts = compileStmt(component, fC, elseStmtId, compileDesign,
                            Reduce::No, nullptr, nullptr, true);
        checkForLoops(false);
        blockNameId = fC->Child(fC->Child(elseStmtId));
        if (fC->Type(blockNameId) == VObjectType::slStringConst) {
          std::string_view blockName = fC->SymName(blockNameId);
          named_begin* stmt = s.MakeNamed_begin();
          stmt->VpiName(blockName);
          stmt->VpiParent(genif);
          genif->VpiElseStmt(stmt);
          if (stmts != nullptr) {
            stmt->Stmts(stmts);
            for (auto s : *stmts) s->VpiParent(stmt);
          }
        } else {
          begin* stmt = s.MakeBegin();
          stmt->VpiParent(genif);
          genif->VpiElseStmt(stmt);
          if (stmts != nullptr) {
            stmt->Stmts(stmts);
            for (auto s : *stmts) s->VpiParent(stmt);
          }
        }
      } else {
        gen_if* genif = s.MakeGen_if();
        genstmt = genif;
        if (cond != nullptr) {
          genif->VpiCondition(cond);
          cond->VpiParent(genif);
        }
        fC->populateCoreMembers(ifElseId, ifElseId, genif);
        ModuleDefinition* subComponent =
            new ModuleDefinition(fC, id, "GENERATE_STMT_PLACEHOLDER");
        component = subComponent;
        checkForLoops(true);
        VectorOfany* stmts = compileStmt(component, fC, stmtId, compileDesign,
                                         Reduce::No, nullptr, nullptr, true);
        checkForLoops(false);
        NodeId blockNameId = fC->Child(fC->Child(stmtId));
        if (fC->Type(blockNameId) == VObjectType::slStringConst) {
          std::string_view blockName = fC->SymName(blockNameId);
          named_begin* stmt = s.MakeNamed_begin();
          stmt->VpiName(blockName);
          stmt->VpiParent(genif);
          genif->VpiStmt(stmt);
          if (stmts != nullptr) {
            stmt->Stmts(stmts);
            for (auto s : *stmts) s->VpiParent(stmt);
          }
        } else {
          begin* stmt = s.MakeBegin();
          stmt->VpiParent(genif);
          genif->VpiStmt(stmt);
          if (stmts != nullptr) {
            stmt->Stmts(stmts);
            for (auto s : *stmts) s->VpiParent(stmt);
          }
        }
      }
    }
  } else if (fC->Type(stmtId) ==
             VObjectType::paCase_generate_construct) {  // Case
    NodeId tmp = fC->Child(stmtId);
    gen_case* gencase = s.MakeGen_case();
    genstmt = gencase;
    checkForLoops(true);
    if (expr* cond = (expr*)compileExpression(component, fC, tmp, compileDesign,
                                              Reduce::No, gencase)) {
      gencase->VpiCondition(cond);
    }
    checkForLoops(false);
    VectorOfcase_item* items = s.MakeCase_itemVec();
    gencase->Case_items(items);
    tmp = fC->Sibling(tmp);
    while (tmp) {
      if (fC->Type(tmp) == VObjectType::paCase_generate_item) {
        NodeId itemExp = fC->Child(tmp);
        expr* ex = nullptr;
        NodeId stmtId = itemExp;
        if (fC->Type(itemExp) == VObjectType::paConstant_expression) {
          checkForLoops(true);
          ex = (expr*)compileExpression(component, fC, itemExp, compileDesign,
                                        Reduce::No);
          checkForLoops(false);
          stmtId = fC->Sibling(stmtId);
        }
        ModuleDefinition* subComponent =
            new ModuleDefinition(fC, id, "GENERATE_STMT_PLACEHOLDER");
        component = subComponent;
        checkForLoops(true);
        VectorOfany* stmts = compileStmt(component, fC, stmtId, compileDesign,
                                         Reduce::No, nullptr, nullptr, true);
        checkForLoops(false);
        case_item* citem = s.MakeCase_item();
        items->push_back(citem);
        VectorOfany* exprs = s.MakeAnyVec();
        citem->VpiExprs(exprs);
        if (ex) {
          ex->VpiParent(citem);
          exprs->push_back(ex);
        }
        NodeId blockNameId = fC->Child(fC->Child(stmtId));
        if (fC->Type(blockNameId) == VObjectType::slStringConst) {
          std::string_view blockName = fC->SymName(blockNameId);
          named_begin* stmt = s.MakeNamed_begin();
          stmt->VpiName(blockName);
          stmt->VpiParent(citem);
          citem->Stmt(stmt);
          if (stmts != nullptr) {
            stmt->Stmts(stmts);
            for (auto s : *stmts) s->VpiParent(stmt);
          }
        } else {
          begin* stmt = s.MakeBegin();
          stmt->VpiParent(citem);
          citem->Stmt(stmt);
          if (stmts != nullptr) {
            stmt->Stmts(stmts);
            for (auto s : *stmts) s->VpiParent(stmt);
          }
        }
      }
      tmp = fC->Sibling(tmp);
    }
  } else if (fC->Type(stmtId) == VObjectType::paGenvar_initialization ||
             fC->Type(stmtId) ==
                 VObjectType::paGenvar_decl_assignment) {  // For loop stmt
    NodeId varInit = stmtId;
    NodeId endLoopTest = fC->Sibling(varInit);
    gen_for* genfor = s.MakeGen_for();
    genstmt = genfor;

    // Var init
    genfor->VpiForInitStmts(s.MakeAnyVec());
    VectorOfany* stmts = genfor->VpiForInitStmts();

    NodeId Var = fC->Child(varInit);
    NodeId Expression = fC->Sibling(Var);
    assignment* assign_stmt = s.MakeAssignment();
    assign_stmt->VpiParent(genfor);
    fC->populateCoreMembers(varInit, varInit, assign_stmt);
    if (variables* varb = (variables*)compileVariable(
            component, fC, Var, compileDesign, Reduce::No, assign_stmt, nullptr,
            /*Mute errors*/ false, /*Implicit int*/ true)) {
      assign_stmt->Lhs(varb);
      varb->VpiParent(assign_stmt);
      varb->VpiName(fC->SymName(Var));
      fC->populateCoreMembers(Var, Var, varb);
    }
    checkForLoops(true);
    if (expr* rhs =
            (expr*)compileExpression(component, fC, Expression, compileDesign,
                                     Reduce::No, assign_stmt)) {
      assign_stmt->Rhs(rhs);
    }
    checkForLoops(false);
    stmts->push_back(assign_stmt);

    // Condition
    checkForLoops(true);
    if (expr* cond = (expr*)compileExpression(
            component, fC, endLoopTest, compileDesign, Reduce::No, genfor)) {
      genfor->VpiCondition(cond);
    }
    checkForLoops(false);

    // Iteration
    NodeId iteration = fC->Sibling(endLoopTest);
    NodeId var = fC->Child(iteration);
    NodeId assignOp = fC->Sibling(var);
    NodeId exprId = fC->Sibling(assignOp);
    if (!exprId) {  // Unary operator like i++
      exprId = iteration;
      checkForLoops(true);
      if (expr* ex = (expr*)compileExpression(
              component, fC, exprId, compileDesign, Reduce::No, genfor)) {
        genfor->VpiForIncStmt(ex);
      }
      checkForLoops(false);
    } else {
      assignment* assign_stmt = s.MakeAssignment();
      assign_stmt->VpiOpType(UhdmWriter::getVpiOpType(fC->Type(assignOp)));
      genfor->VpiForIncStmt(assign_stmt);
      assign_stmt->VpiParent(genfor);
      fC->populateCoreMembers(iteration, iteration, assign_stmt);
      checkForLoops(true);
      if (expr* lhs = (expr*)compileExpression(
              component, fC, var, compileDesign, Reduce::No, assign_stmt)) {
        assign_stmt->Lhs(lhs);
      }
      if (expr* rhs = (expr*)compileExpression(
              component, fC, exprId, compileDesign, Reduce::No, assign_stmt)) {
        assign_stmt->Rhs(rhs);
      }
      checkForLoops(false);
    }

    // Stmts
    NodeId genBlock = fC->Sibling(iteration);
    ModuleDefinition* subComponent =
        new ModuleDefinition(fC, id, "GENERATE_STMT_PLACEHOLDER");
    component = subComponent;
    checkForLoops(true);
    stmts = compileStmt(component, fC, genBlock, compileDesign, Reduce::No,
                        nullptr, nullptr, true);
    checkForLoops(false);
    NodeId blockNameId = fC->Child(fC->Child(genBlock));
    if (fC->Type(blockNameId) == VObjectType::slStringConst) {
      std::string_view blockName = fC->SymName(blockNameId);
      named_begin* stmt = s.MakeNamed_begin();
      stmt->VpiName(blockName);
      stmt->VpiParent(genfor);
      genfor->VpiStmt(stmt);
      if (stmts != nullptr) {
        stmt->Stmts(stmts);
        for (auto s : *stmts) s->VpiParent(stmt);
      }
    } else {
      begin* stmt = s.MakeBegin();
      stmt->VpiParent(genfor);
      genfor->VpiStmt(stmt);
      if (stmts != nullptr) {
        stmt->Stmts(stmts);
        for (auto s : *stmts) s->VpiParent(stmt);
      }
    }
  }
  VectorOfgen_stmt* stmts = s.MakeGen_stmtVec();
  if (genstmt) stmts->push_back(genstmt);
  return stmts;
}

}  // namespace SURELOG
