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
 * File:   TaskMethod.h
 * Author: alain
 *
 * Created on February 21, 2019, 8:21 PM
 */

#ifndef SURELOG_TASKMETHOD_H
#define SURELOG_TASKMETHOD_H
#pragma once

#include <Surelog/Common/NodeId.h>
#include <Surelog/Design/Task.h>
#include <Surelog/DesignCompile/CompileHelper.h>

#include <string_view>

namespace SURELOG {

class TaskMethod final : public Task {
 public:
  TaskMethod(DesignComponent* parent, const FileContent* fC, NodeId id,
             std::string_view name, bool is_extern)
      : Task(parent, fC, id, name), m_extern(is_extern) {}
  ~TaskMethod() final = default;
  bool isExtern() const { return m_extern; }
  bool compile(CompileHelper& compile_helper);

 private:
  bool m_extern;
};

};  // namespace SURELOG

#endif /* SURELOG_TASKMETHOD_H */
