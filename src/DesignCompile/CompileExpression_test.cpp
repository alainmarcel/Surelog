/*
 Copyright 2021 Alain Dargelas

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

#include <gmock/gmock.h>
#include <gtest/gtest.h>

#include <memory>
#include <string>
#include <vector>

#include "Surelog/Design/FileContent.h"
#include "Surelog/DesignCompile/CompileDesign.h"
#include "Surelog/DesignCompile/CompileHelper.h"
#include "Surelog/DesignCompile/CompilerHarness.h"
#include "Surelog/SourceCompile/ParserHarness.h"
#include "Surelog/SourceCompile/PreprocessHarness.h"
#include "Surelog/SourceCompile/VObjectTypes.h"

// UHDM
#include <uhdm/ExprEval.h>
#include <uhdm/expr.h>
#include <uhdm/uhdm_types.h>

namespace SURELOG {

using ::testing::ElementsAre;

namespace {
TEST(CompileExpression, ExprFromParseTree1) {
  CompileHelper helper;
  ParserHarness pharness;
  CompilerHarness charness;
  std::unique_ptr<CompileDesign> compileDesign = charness.createCompileDesign();
  // Cannot use parameters assignments in next expression, there is no
  // elaboration performed here!
  auto fC = pharness.parse(
      "module top();"
      "parameter p1 = 1 << 4;"
      "parameter p2 = (1 << 8) >> 4;"
      "parameter p3 = (16 * 4) / 4;"
      "parameter p4 = 32 - 16;"
      "parameter p5 = 2 ** 4;"
      "parameter p6 = (1'b1) ? 16 : 15;"
      "parameter p7 = (1'b0) ? 15 : 16;"
      "endmodule");
  NodeId root = fC->getRootNode();
  std::vector<NodeId> assigns =
      fC->sl_collect_all(root, VObjectType::paParam_assignment);
  EXPECT_EQ(assigns.size(), 7);
  for (NodeId param_assign : assigns) {
    NodeId param = fC->Child(param_assign);
    NodeId rhs = fC->Sibling(param);
    const UHDM::expr *exp = (UHDM::expr *)helper.compileExpression(
        nullptr, fC.get(), rhs, compileDesign.get(), Reduce::Yes, nullptr,
        nullptr, true);
    EXPECT_EQ(exp->UhdmType(), UHDM::uhdmconstant);
    bool invalidValue = false;
    UHDM::ExprEval eval;
    EXPECT_EQ(eval.get_value(invalidValue, exp), 16);
  }
}
TEST(CompileExpression, ExprFromParseTree2) {
  CompileHelper helper;
  ParserHarness pharness;
  CompilerHarness charness;
  std::unique_ptr<CompileDesign> compileDesign = charness.createCompileDesign();
  // Cannot use parameters assignments in next expression, there is no
  // elaboration performed here!
  auto fC = pharness.parse(
      "module top();"
      "parameter p1 = 1'b1 | 1'b0;"
      "parameter p2 = 1'b1 & 1'b1;"
      "parameter p3 = !1'b0;"
      "parameter p4 = ~1'b0;"
      "endmodule");
  NodeId root = fC->getRootNode();
  std::vector<NodeId> assigns =
      fC->sl_collect_all(root, VObjectType::paParam_assignment);
  EXPECT_EQ(assigns.size(), 4);
  for (NodeId param_assign : assigns) {
    NodeId param = fC->Child(param_assign);
    NodeId rhs = fC->Sibling(param);
    const UHDM::expr *exp = (UHDM::expr *)helper.compileExpression(
        nullptr, fC.get(), rhs, compileDesign.get(), Reduce::Yes, nullptr,
        nullptr, true);
    EXPECT_EQ(exp->UhdmType(), UHDM::uhdmconstant);
    bool invalidValue = false;
    UHDM::ExprEval eval;
    EXPECT_EQ(eval.get_value(invalidValue, exp), 1);
  }
}
TEST(CompileExpression, ExprFromParseTree3) {
  CompileHelper helper;
  ParserHarness pharness;
  CompilerHarness charness;
  std::unique_ptr<CompileDesign> compileDesign = charness.createCompileDesign();
  // Cannot use parameters assignments in next expression, there is no
  // elaboration performed here!
  auto fC = pharness.parse(
      "module top();"
      "parameter p1 = {1'b1, 2'b10}"
      "parameter p2 = '{1'b1, 2'b10}"
      "endmodule");
  NodeId root = fC->getRootNode();
  std::vector<NodeId> assigns =
      fC->sl_collect_all(root, VObjectType::paParam_assignment);
  EXPECT_EQ(assigns.size(), 2);
  for (NodeId param_assign : assigns) {
    NodeId param = fC->Child(param_assign);
    const std::string_view name = fC->SymName(param);
    NodeId rhs = fC->Sibling(param);
    const UHDM::expr *exp1 = (UHDM::expr *)helper.compileExpression(
        nullptr, fC.get(), rhs, compileDesign.get(), Reduce::No, nullptr,
        nullptr, true);
    EXPECT_EQ(exp1->UhdmType(), UHDM::uhdmoperation);
    const UHDM::expr *exp2 = (UHDM::expr *)helper.compileExpression(
        nullptr, fC.get(), rhs, compileDesign.get(), Reduce::Yes, nullptr,
        nullptr, true);
    if (name == "p1") {
      EXPECT_EQ(exp2->UhdmType(), UHDM::uhdmconstant);
      bool invalidValue = false;
      UHDM::ExprEval eval;
      EXPECT_EQ(eval.get_value(invalidValue, exp2), 6);
    }
  }
}
TEST(CompileExpression, ExprFromPpTree) {
  CompileHelper helper;
  PreprocessHarness ppharness;
  ParserHarness pharness;
  CompilerHarness charness;
  std::unique_ptr<CompileDesign> compileDesign = charness.createCompileDesign();
  const std::string text = ppharness.preprocess(
      "`define A {1'b1, 2'b10}\n"
      "\n"
      "`define B '{1'b1, 2'b10}\n"
      "\n"
      "module top();\n"
      "parameter p1 = `A;\n"
      "parameter p2 = `B;\n"
      "endmodule\n");
  // Cannot use parameters assignments in next expression, there is no
  // elaboration performed here!
  auto fC = pharness.parse(text);
  NodeId root = fC->getRootNode();
  std::vector<NodeId> assigns =
      fC->sl_collect_all(root, VObjectType::paParam_assignment);
  EXPECT_EQ(assigns.size(), 2);
  for (NodeId param_assign : assigns) {
    NodeId param = fC->Child(param_assign);
    const std::string_view name = fC->SymName(param);
    NodeId rhs = fC->Sibling(param);
    const UHDM::expr *exp1 = (UHDM::expr *)helper.compileExpression(
        nullptr, fC.get(), rhs, compileDesign.get(), Reduce::No, nullptr,
        nullptr, true);
    EXPECT_EQ(exp1->UhdmType(), UHDM::uhdmoperation);
    const UHDM::expr *exp2 = (UHDM::expr *)helper.compileExpression(
        nullptr, fC.get(), rhs, compileDesign.get(), Reduce::Yes, nullptr,
        nullptr, true);
    if (name == "p1") {
      EXPECT_EQ(exp2->UhdmType(), UHDM::uhdmconstant);
      bool invalidValue = false;
      UHDM::ExprEval eval;
      EXPECT_EQ(eval.get_value(invalidValue, exp2), 6);
    }
  }
}
}  // namespace
}  // namespace SURELOG
