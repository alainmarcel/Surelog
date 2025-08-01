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
 * File:   ConfigSet.cpp
 * Author: alain
 *
 * Created on February 10, 2018, 11:14 PM
 */

#include "Surelog/Config/ConfigSet.h"

#include <string_view>

#include "Surelog/Config/Config.h"

namespace SURELOG {
Config* ConfigSet::getMutableConfigByName(std::string_view configName) {
  for (auto& config : m_configs) {
    if (config.getName() == configName) return &config;
  }
  return nullptr;
}
}  // namespace SURELOG
