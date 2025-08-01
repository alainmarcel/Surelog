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
 * File:   Location.cpp
 * Author: alain
 *
 * Created on March 6, 2017, 6:48 PM
 */

#include "Surelog/ErrorReporting/Location.h"

#include <ostream>

#include "Surelog/Common/PathId.h"
#include "Surelog/Common/SymbolId.h"

namespace SURELOG {

bool Location::operator==(const Location &rhs) const {
  if (m_fileId != rhs.m_fileId) return false;
  if (m_line != rhs.m_line) return false;
  if (m_column != rhs.m_column) return false;
  if (m_object != rhs.m_object) return false;
  return true;
}

bool Location::operator<(const Location &rhs) const {
  static PathIdLessThanComparer pathIdComparer;
  static SymbolIdLessThanComparer symbolIdComparer;
  if (pathIdComparer(m_fileId, rhs.m_fileId)) return true;
  if (m_line < rhs.m_line) return true;
  if (m_column < rhs.m_column) return true;
  if (symbolIdComparer(m_object, rhs.m_object)) return true;
  return false;
}

std::ostream &operator<<(std::ostream &strm, const Location &location) {
  strm << "file-id=" << location.m_fileId << ", "
       << "line=" << location.m_line << ", "
       << "column=" << location.m_column << ", "
       << "object=" << location.m_object;
  return strm;
}

}  // namespace SURELOG
