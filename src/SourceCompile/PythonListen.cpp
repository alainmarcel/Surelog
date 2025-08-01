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

/* parserAntlrHandler
 * File:   PythonListen.cpp
 * Author: alainparserAntlrHandler
 *
 * Created on June 4, 2017, 8:09 PM
 */

#include "Surelog/SourceCompile/PythonListen.h"

#ifdef SURELOG_WITH_PYTHON

#include "Surelog/API/SV3_1aPythonListener.h"
#include "Surelog/Cache/PythonAPICache.h"
#include "Surelog/ErrorReporting/Error.h"
#include "Surelog/ErrorReporting/ErrorContainer.h"
#include "Surelog/SourceCompile/AntlrParserHandler.h"
#include "Surelog/SourceCompile/CompileSourceFile.h"

namespace SURELOG {

PythonListen::PythonListen(ParseFile* parse,
                           CompileSourceFile* compileSourceFile)
    : m_parse(parse),
      m_compileSourceFile(compileSourceFile),
      m_usingCachedVersion(false) {}

PythonListen::~PythonListen() = default;

void PythonListen::addError(Error& error) {
  getCompileSourceFile()->getErrorContainer()->addError(error);
}

bool PythonListen::listen() {
  PythonAPICache cache(this);
  if (cache.restore()) {
    m_usingCachedVersion = true;
    return true;
  }

  // This is either a parent Parser object of this Parser object has no parent
  if ((!m_parse->m_children.empty()) || (m_parse->m_parent == nullptr)) {
    if ((m_parse->m_parent == nullptr) && (m_parse->m_children.empty())) {
      SV3_1aPythonListener* pythonListener =
          new SV3_1aPythonListener(this, m_compileSourceFile->getPythonInterp(),
                                   m_parse->m_antlrParserHandler->m_tokens, 0);
      m_pythonListeners.push_back(pythonListener);
      antlr4::tree::ParseTreeWalker::DEFAULT.walk(
          pythonListener, m_parse->m_antlrParserHandler->m_tree);
    }

    if (!m_parse->m_children.empty()) {
      for (const ParseFile* child : m_parse->m_children) {
        if (child->m_antlrParserHandler) {
          // Only visit the chunks that got re-parsed
          // TODO: Incrementally regenerate the FileContent

          SV3_1aPythonListener* pythonListener = new SV3_1aPythonListener(
              this, m_compileSourceFile->getPythonInterp(),
              child->m_antlrParserHandler->m_tokens, child->m_offsetLine);
          m_pythonListeners.push_back(pythonListener);
          antlr4::tree::ParseTreeWalker::DEFAULT.walk(
              pythonListener, child->m_antlrParserHandler->m_tree);
        }
      }
    }
  }

  if (!cache.save()) {
    return false;
  }

  return true;
}
}  // namespace SURELOG
#endif  // SURELOG_WITH_PYTHON
