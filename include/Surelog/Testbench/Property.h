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
 * File:   Property.h
 * Author: alain
 *
 * Created on January 23, 2019, 9:17 PM
 */

#ifndef SURELOG_PROPERTY_H
#define SURELOG_PROPERTY_H
#pragma once

#include <Surelog/Common/NodeId.h>
#include <Surelog/Testbench/Variable.h>

#include <string_view>

namespace SURELOG {

class DataType;
class FileContent;

class Property final : public Variable {
 public:
  Property(DataType* dataType, const FileContent* fc, NodeId varId,
           NodeId range, std::string_view name, bool is_local, bool is_static,
           bool is_protected, bool is_rand, bool is_randc)
      : Variable(dataType, fc, varId, range, name),
        m_is_local(is_local),
        m_is_static(is_static),
        m_is_protected(is_protected),
        m_is_rand(is_rand),
        m_is_randc(is_randc) {}
  ~Property() final = default;

  bool isLocal() const { return m_is_local; }
  bool isStatic() const { return m_is_static; }
  bool isProtected() const { return m_is_protected; }
  bool isRand() const { return m_is_rand; }
  bool isRandc() const { return m_is_randc; }

 private:
  const bool m_is_local;
  const bool m_is_static;
  const bool m_is_protected;
  const bool m_is_rand;
  const bool m_is_randc;
};

};  // namespace SURELOG

#endif /* SURELOG_PROPERTY_H */
