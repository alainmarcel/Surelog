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
 * File:   PythonAPI.cpp
 * Author: alain
 *
 * Created on May 13, 2017, 4:42 PM
 */

#include "Surelog/API/PythonAPI.h"

#include <cstdint>
#include <cstdio>
#include <cstring>
#include <filesystem>
#include <string>
#include <vector>

#include "Surelog/Design/Design.h"
#include "Surelog/ErrorReporting/ErrorContainer.h"
#include "Surelog/Utils/StringUtils.h"

#ifdef SURELOG_WITH_PYTHON
#include <Python.h>

#include <iostream>
#include <memory>

#include "Surelog/API/SLAPI.h"
#include "Surelog/API/SV3_1aPythonListener.h"
#include "Surelog/API/VObjectTypes_py.h"
#include "Surelog/API/slapi_scripts.h"
#include "Surelog/Common/FileSystem.h"
#include "Surelog/Common/NodeId.h"
#include "Surelog/Common/PathId.h"
#include "Surelog/SourceCompile/SymbolTable.h"

using NodeId = SURELOG::NodeId;
#include <Surelog/API/slapi_wrap.cxx>  // NOLINT(bugprone-suspicious-include)
#endif

namespace SURELOG {
std::string PythonAPI::m_invalidScriptResult = "INVALID_PYTHON_SCRIPT_RESULT";

PyThreadState* PythonAPI::m_mainThreadState = nullptr;

std::filesystem::path PythonAPI::m_programPath;

bool PythonAPI::m_listenerLoaded = false;

std::filesystem::path PythonAPI::m_listenerScript;

bool PythonAPI::m_strictMode = false;

std::filesystem::path PythonAPI::m_builtinPath;

#ifdef SURELOG_WITH_PYTHON
static struct PyModuleDef SLAPI_module = {PyModuleDef_HEAD_INIT,
                                          "slapi",
                                          nullptr,
                                          -1,
                                          SwigMethods,
                                          nullptr,
                                          nullptr,
                                          nullptr,
                                          nullptr};

static PyObject* PyInit_slapi() { return PyModule_Create(&SLAPI_module); }
#endif

void PythonAPI::shutdown() {
#ifdef SURELOG_WITH_PYTHON
  PyEval_RestoreThread(m_mainThreadState);
  Py_Finalize();
#endif
}

bool PythonAPI::loadScript(const std::filesystem::path& name, bool check) {
#ifdef SURELOG_WITH_PYTHON
  PyEval_AcquireThread(m_mainThreadState);
  bool status = loadScript_(name, check);
  PyEval_ReleaseThread(m_mainThreadState);
  return status;
#else
  return false;
#endif
}

bool PythonAPI::loadScript_(const std::filesystem::path& name, bool check) {
#ifdef SURELOG_WITH_PYTHON
  FileSystem* const fileSystem = FileSystem::getInstance();
  std::unique_ptr<SymbolTable> symbolTable(new SymbolTable);
  PathId nameId = fileSystem->toPathId(name.string(), symbolTable.get());
  if (fileSystem->isRegularFile(nameId)) {
    std::string fname = name.string();
    FILE* fp = fopen(fname.c_str(), "r");
    PyRun_SimpleFile(fp, fname.c_str());
    PyErr_Print();
    fclose(fp);
    return true;
  } else {
    if (check)
      std::cerr << "PYTHON API ERROR: Script \"" << name
                << "\" does not exist.\n";
  }
#endif
  return false;
}

PyThreadState* PythonAPI::initNewInterp() {
#ifdef SURELOG_WITH_PYTHON
  PyEval_AcquireThread(m_mainThreadState);
  PyThreadState* interpState = Py_NewInterpreter();

  m_listenerLoaded = false;

  initInterp_();
  loadScriptsInInterp_();
  // PyEval_ReleaseThread(m_mainThreadState);

  PyEval_ReleaseThread(interpState);
  return interpState;
#else
  return nullptr;
#endif
}

void PythonAPI::shutdown(PyThreadState* interp) {
#ifdef SURELOG_WITH_PYTHON
  if (interp != m_mainThreadState) {
    PyGILState_STATE gstate = PyGILState_Ensure();
    PyThreadState* old_state = PyThreadState_Swap(interp);
    Py_EndInterpreter(interp);
    PyThreadState_Swap(old_state);
    PyGILState_Release(gstate);
  }
#endif
}

void PythonAPI::loadScriptsInInterp_() {
#ifdef SURELOG_WITH_PYTHON
  FileSystem* const fileSystem = FileSystem::getInstance();
  std::unique_ptr<SymbolTable> symbolTable(new SymbolTable);

  const std::filesystem::path workingDir = fileSystem->getWorkingDir();

  bool waiverLoaded = false;
  std::filesystem::path waivers = workingDir / "slwaivers.py";
  PathId waiversId = fileSystem->toPathId(waivers.string(), symbolTable.get());
  if (fileSystem->isRegularFile(waiversId)) {
    waiverLoaded = loadScript_(waivers);
  }

  if (!waiverLoaded) {
    waivers = m_programPath / "python" / "slwaivers.py";
    waiversId = fileSystem->toPathId(waivers.string(), symbolTable.get());
    if (fileSystem->isRegularFile(waiversId)) {
      waiverLoaded = loadScript_(waivers);
    }
  }

  bool messageFormatLoaded = false;
  std::filesystem::path format = workingDir / "slformatmsg.py";
  PathId formatId = fileSystem->toPathId(format.string(), symbolTable.get());
  if (fileSystem->isRegularFile(formatId)) {
    messageFormatLoaded = loadScript_(format);
  }

  if (!messageFormatLoaded) {
    format = m_programPath / "python" / "slformatmsg.py";
    formatId = fileSystem->toPathId(format.string(), symbolTable.get());
    if (fileSystem->isRegularFile(formatId)) {
      messageFormatLoaded = loadScript_(format);
    }
  }

  if (!m_listenerScript.empty()) {
    PathId listenerId =
        fileSystem->toPathId(m_listenerScript.string(), symbolTable.get());
    if (fileSystem->isRegularFile(listenerId)) {
      m_listenerLoaded = loadScript_(m_listenerScript);
    }
  }

  if (!m_listenerLoaded) {
    std::filesystem::path listener = workingDir / "slSV3_1aPythonListener.py";
    PathId listenerId =
        fileSystem->toPathId(listener.string(), symbolTable.get());
    if (fileSystem->isRegularFile(listenerId)) {
      m_listenerScript = listener;
      m_listenerLoaded = loadScript_(listener);
    }
  }

  if (!m_listenerLoaded) {
    std::filesystem::path listener =
        m_programPath / "python" / "slSV3_1aPythonListener.py";
    PathId listenerId =
        fileSystem->toPathId(listener.string(), symbolTable.get());
    if (fileSystem->isRegularFile(listenerId)) {
      m_listenerScript = listener;
      m_listenerLoaded = loadScript_(listener);
    }
  }
#endif
}

void PythonAPI::loadScripts() {
#ifdef SURELOG_WITH_PYTHON
  PyEval_AcquireThread(m_mainThreadState);

  loadScriptsInInterp_();

  PyEval_ReleaseThread(m_mainThreadState);
#endif
}

void PythonAPI::initInterp_() {
#ifdef SURELOG_WITH_PYTHON
  // Loads the python SWIG generated defs
  std::string script;
  for (auto s : slapi_scripts) {
    script += s;
  }
  for (auto s : slapi_types) {
    script += s;
  }
  PyRun_SimpleString(script.c_str());

  PyRun_SimpleString("import sys");
  PyRun_SimpleString("sys.path.append(\".\")");
  PyRun_SimpleString(
      std::string("sys.path.append(\"" + m_programPath.string() + "\")")
          .c_str());
#endif
}

void PythonAPI::init(int32_t argc, const char** argv) {
  std::string programPath = argv[0];
  programPath = StringUtils::replaceAll(programPath, "\\", "/");
  m_programPath = StringUtils::rtrim_until(programPath, '/');
  for (int32_t i = 1; i < argc; i++) {
    if (!strcmp(argv[i], "-builtin")) {
      if (i < argc - 1) {
        m_builtinPath = argv[i + 1];
      }
    }
  }
  // Before Python 3.7, the parameter to SetProgramName() was not a
  // const wchar_t* but a wchar_t (even though never written to).
#ifdef SURELOG_WITH_PYTHON
  static wchar_t progname[] = L"surelog";

  Py_SetProgramName(progname);

  PyImport_AppendInittab("slapi", &PyInit_slapi);

  Py_Initialize();
  PyEval_InitThreads();
  m_mainThreadState = PyEval_SaveThread();
  PyEval_AcquireThread(m_mainThreadState);

  initInterp_();

  PyEval_ReleaseThread(m_mainThreadState);
#endif
}

void PythonAPI::evalScript(const std::string& function,
                           SV3_1aPythonListener* listener,
                           parser_rule_context* ctx1) {
#ifdef SURELOG_WITH_PYTHON
  antlr4::ParserRuleContext* ctx = (antlr4::ParserRuleContext*)ctx1;
  PyEval_AcquireThread(listener->getPyThreadState());
  PyObject *pModuleName, *pModule, *pFunc;
  PyObject *pArgs, *pValue;
  pModuleName = PyString_FromString("__main__");
  pModule = PyImport_Import(pModuleName);
  Py_DECREF(pModuleName);
  pFunc = PyObject_GetAttrString(pModule, function.c_str());
  if (!pFunc || !PyCallable_Check(pFunc)) {
    if (m_strictMode)
      std::cout << "PYTHON API ERROR: Function \"" << function
                << "\" does not exist.\n";
    PyEval_ReleaseThread(listener->getPyThreadState());
    return;
  }
  pArgs = PyTuple_New(2);
  pValue = SWIG_NewPointerObj(SWIG_as_voidptr(listener),
                              SWIGTYPE_p_SURELOG__SV3_1aPythonListener, 0 | 0);
  PyTuple_SetItem(pArgs, 0, pValue);
  pValue = SWIG_NewPointerObj(SWIG_as_voidptr(ctx),
                              SWIGTYPE_p_antlr4__ParserRuleContext, 0 | 0);
  PyTuple_SetItem(pArgs, 1, pValue);
  PyObject_CallObject(pFunc, pArgs);
  PyErr_Print();
  Py_DECREF(pArgs);
  Py_XDECREF(pFunc);
  Py_DECREF(pModule);
  PyEval_ReleaseThread(listener->getPyThreadState());
#endif
}

std::string PythonAPI::evalScript(const std::string& module,
                                  const std::string& function,
                                  const std::vector<std::string>& args,
                                  PyThreadState* interp) {
#ifdef SURELOG_WITH_PYTHON
  PyEval_AcquireThread(interp);

  std::string result;
  PyObject *pModuleName, *pModule, *pFunc;
  PyObject *pArgs, *pValue;

  pModuleName = PyString_FromString(module.c_str());
  pModule = PyImport_Import(pModuleName);

  Py_DECREF(pModuleName);
  if (pModule != nullptr) {
    pFunc = PyObject_GetAttrString(pModule, function.c_str());
    /* pFunc is a new reference */

    if (pFunc && PyCallable_Check(pFunc)) {
      pArgs = PyTuple_New(args.size());
      for (uint32_t i = 0; i < args.size(); ++i) {
        pValue = PyString_FromString(args[i].c_str());
        /* pValue reference stolen here: */
        PyTuple_SetItem(pArgs, i, pValue);
      }
      pValue = PyObject_CallObject(pFunc, pArgs);
      Py_DECREF(pArgs);
      if (pValue != nullptr) {
        Py_ssize_t size;
        const char* compName = PyUnicode_AsUTF8AndSize(pValue, &size);
        if (compName == nullptr) {
          std::cout << "PYTHON API ERROR: Incorrect function return type, "
                       "expecting a string: "
                    << function << std::endl;
          Py_DECREF(pValue);

          PyEval_ReleaseThread(interp);
          return m_invalidScriptResult;
        }
        result = compName;
        Py_DECREF(pValue);
      } else {
        Py_DECREF(pFunc);
        Py_DECREF(pModule);
        PyErr_Print();
        std::cout << "PYTHON API ERROR: Incorrect function evaluation: "
                  << function << std::endl;
        PyEval_ReleaseThread(interp);
        return m_invalidScriptResult;
      }
    } else {
      if (PyErr_Occurred()) PyErr_Print();
      std::cout << "PYTHON API ERROR: Cannot find function " << function
                << std::endl;

      PyEval_ReleaseThread(interp);
      return m_invalidScriptResult;
    }
    Py_XDECREF(pFunc);
    Py_DECREF(pModule);
  } else {
    PyErr_Print();
    std::cout << "PYTHON API ERROR: Cannot load module " << module << std::endl;
    return m_invalidScriptResult;
  }

  PyEval_ReleaseThread(interp);
  return result;
#else
  return "";
#endif
}

bool PythonAPI::evalScriptPerFile(const std::filesystem::path& script,
                                  ErrorContainer* errors, FileContent* fC,
                                  PyThreadState* interp) {
#ifdef SURELOG_WITH_PYTHON
  PyEval_AcquireThread(interp);
  loadScript_(script);
  std::string function = "slUserCallbackPerFile";
  PyObject *pModuleName, *pModule, *pFunc;
  PyObject *pArgs, *pValue;
  pModuleName = PyString_FromString("__main__");
  pModule = PyImport_Import(pModuleName);
  Py_DECREF(pModuleName);
  pFunc = PyObject_GetAttrString(pModule, function.c_str());
  if (!pFunc || !PyCallable_Check(pFunc)) {
    std::cout << "PYTHON API ERROR: Function \"" << function
              << "\" does not exist.\n";
    PyEval_ReleaseThread(interp);
    return false;
  }
  pArgs = PyTuple_New(2);
  pValue = SWIG_NewPointerObj(SWIG_as_voidptr(errors),
                              SWIGTYPE_p_SURELOG__ErrorContainer, 0 | 0);
  PyTuple_SetItem(pArgs, 0, pValue);
  pValue = SWIG_NewPointerObj(SWIG_as_voidptr(fC),
                              SWIGTYPE_p_SURELOG__FileContent, 0 | 0);
  PyTuple_SetItem(pArgs, 1, pValue);

  PyObject_CallObject(pFunc, pArgs);
  PyErr_Print();
  Py_DECREF(pArgs);
  Py_XDECREF(pFunc);
  Py_DECREF(pModule);

  PyEval_ReleaseThread(interp);
  return true;
#else
  return false;
#endif
}

bool PythonAPI::evalScript(const std::filesystem::path& script,
                           Design* design) {
#ifdef SURELOG_WITH_PYTHON
  PyEval_AcquireThread(m_mainThreadState);
  loadScript_(script);
  std::string function = "slUserCallbackPerDesign";
  PyObject *pModuleName, *pModule, *pFunc;
  PyObject *pArgs, *pValue;
  pModuleName = PyString_FromString("__main__");
  pModule = PyImport_Import(pModuleName);
  Py_DECREF(pModuleName);
  pFunc = PyObject_GetAttrString(pModule, function.c_str());
  if (!pFunc || !PyCallable_Check(pFunc)) {
    std::cout << "PYTHON API ERROR: Function \"" << function
              << "\" does not exist.\n";
    PyEval_ReleaseThread(m_mainThreadState);
    return false;
  }
  pArgs = PyTuple_New(2);
  pValue = SWIG_NewPointerObj(SWIG_as_voidptr(design->getErrorContainer()),
                              SWIGTYPE_p_SURELOG__ErrorContainer, 0 | 0);
  PyTuple_SetItem(pArgs, 0, pValue);
  pValue = SWIG_NewPointerObj(SWIG_as_voidptr(design),
                              SWIGTYPE_p_SURELOG__Design, 0 | 0);
  PyTuple_SetItem(pArgs, 1, pValue);
  PyObject_CallObject(pFunc, pArgs);
  PyErr_Print();
  Py_DECREF(pArgs);
  Py_XDECREF(pFunc);
  Py_DECREF(pModule);

  PyEval_ReleaseThread(m_mainThreadState);
  return true;
#else
  return false;
#endif
}

}  // namespace SURELOG
