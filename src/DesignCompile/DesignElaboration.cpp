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
 * File:   DesignElaboration.cpp
 * Author: alain
 *
 * Created on July 12, 2017, 8:55 PM
 */

#include "Surelog/DesignCompile/DesignElaboration.h"

#include "Surelog/CommandLine/CommandLineParser.h"
#include "Surelog/Common/FileSystem.h"
#include "Surelog/Common/NodeId.h"
#include "Surelog/Common/PathId.h"
#include "Surelog/Common/SymbolId.h"
#include "Surelog/Config/Config.h"
#include "Surelog/Config/ConfigSet.h"
#include "Surelog/Design/BindStmt.h"
#include "Surelog/Design/DefParam.h"
#include "Surelog/Design/DesignElement.h"
#include "Surelog/Design/FileCNodeId.h"
#include "Surelog/Design/FileContent.h"
#include "Surelog/Design/ModuleDefinition.h"
#include "Surelog/Design/ModuleInstance.h"
#include "Surelog/Design/Parameter.h"
#include "Surelog/DesignCompile/CompileDesign.h"
#include "Surelog/DesignCompile/CompileHelper.h"
#include "Surelog/DesignCompile/CompileModule.h"
#include "Surelog/DesignCompile/NetlistElaboration.h"
#include "Surelog/DesignCompile/TestbenchElaboration.h"
#include "Surelog/DesignCompile/UhdmWriter.h"
#include "Surelog/ErrorReporting/Error.h"
#include "Surelog/ErrorReporting/ErrorDefinition.h"
#include "Surelog/ErrorReporting/Location.h"
#include "Surelog/Library/Library.h"
#include "Surelog/Package/Package.h"
#include "Surelog/SourceCompile/Compiler.h"
#include "Surelog/SourceCompile/SymbolTable.h"
#include "Surelog/SourceCompile/VObjectTypes.h"
#include "Surelog/Testbench/Program.h"
#include "Surelog/Utils/StringUtils.h"

// UHDM
#include <uhdm/BaseClass.h>
#include <uhdm/ElaboratorListener.h>
#include <uhdm/ExprEval.h>
#include <uhdm/clone_tree.h>
#include <uhdm/expr.h>
#include <uhdm/sv_vpi_user.h>
#include <uhdm/uhdm.h>
#include <uhdm/uhdm_types.h>
#include <uhdm/vpi_user.h>
#include <uhdm/vpi_visitor.h>

#include <algorithm>
#include <cstdint>
#include <cstring>
#include <functional>
#include <iostream>
#include <map>
#include <queue>
#include <set>
#include <string>
#include <unordered_set>
#include <utility>
#include <vector>

namespace SURELOG {
DesignElaboration::DesignElaboration(CompileDesign* compileDesign)
    : TestbenchElaboration(compileDesign) {
  m_moduleDefFactory = nullptr;
  m_moduleInstFactory = nullptr;
  m_exprBuilder.seterrorReporting(
      m_compileDesign->getCompiler()->getErrorContainer(),
      m_compileDesign->getCompiler()->getSymbolTable());
  m_exprBuilder.setDesign(m_compileDesign->getCompiler()->getDesign());
}

DesignElaboration::~DesignElaboration() = default;

bool DesignElaboration::elaborate() {
  createBuiltinPrimitives_();
  setupConfigurations_();
  identifyTopModules_();
  bindPackagesDataTypes_();
  elaborateAllModules_(true);
  elaborateAllModules_(false);
  reduceUnnamedBlocks_();
  bindTypedefsPostElab_();
  checkElaboration_();
  reportElaboration_();
  createFileList_();
  return true;
}

bool DesignElaboration::setupConfigurations_() {
  ConfigSet* configSet =
      m_compileDesign->getCompiler()->getDesign()->getConfigSet();
  SymbolTable* st =
      m_compileDesign->getCompiler()->getCommandLineParser()->getSymbolTable();
  std::vector<Config>& allConfigs = configSet->getAllMutableConfigs();
  std::vector<SymbolId> selectedConfigIds =
      m_compileDesign->getCompiler()->getCommandLineParser()->getUseConfigs();
  std::set<std::string, std::less<>> selectedConfigs;
  for (const auto& confId : selectedConfigIds) {
    std::string name(st->getSymbol(confId));
    if (name.find('.') == std::string::npos) {
      name = StrCat("work@", name);
    } else {
      name = StringUtils::replaceAll(name, ".", "@");
    }
    selectedConfigs.insert(name);
    bool found = false;
    for (const auto& config : allConfigs) {
      if (config.getName() == name) {
        found = true;
        break;
      }
    }
    if (!found) {
      Location loc(st->registerSymbol(name));
      Error err(ErrorDefinition::CMD_UNDEFINED_CONFIG, loc);
      m_compileDesign->getCompiler()->getErrorContainer()->addError(err);
    }
  }

  std::queue<std::string_view> configq;
  for (auto& config : allConfigs) {
    if (selectedConfigs.find(config.getName()) != selectedConfigs.end()) {
      config.setIsUsed();
      config.setTopLevel(true);
      configq.emplace(config.getName());
    }
  }
  std::unordered_set<const Config*> configS;
  while (!configq.empty()) {
    std::string_view configName = configq.front();
    Config* conf = configSet->getMutableConfigByName(configName);
    configq.pop();
    if (conf) {
      if (configS.find(conf) != configS.end()) {
        continue;
      }
      configS.insert(conf);

      conf->setIsUsed();
      for (const auto& usec : conf->getInstanceUseClauses()) {
        if (usec.second.getType() == UseClause::UseConfig) {
          const std::string_view confName = usec.second.getName();
          configq.emplace(confName);
          Config* conf = configSet->getMutableConfigByName(confName);
          if (!conf) {
            const FileContent* fC = usec.second.getFileContent();
            Location loc(fC->getFileId(usec.second.getNodeId()),
                         fC->Line(usec.second.getNodeId()),
                         fC->Column(usec.second.getNodeId()),
                         st->registerSymbol(confName));
            Error err(ErrorDefinition::ELAB_UNDEFINED_CONFIG, loc);
            m_compileDesign->getCompiler()->getErrorContainer()->addError(err);
          }
        }
      }
    }
  }

  std::vector<std::string_view> unused;
  for (const auto& config : allConfigs) {
    const std::string_view name = config.getName();
    const FileContent* fC = config.getFileContent();
    Location loc(fC->getFileId(config.getNodeId()),
                 fC->Line(config.getNodeId()), fC->Column(config.getNodeId()),
                 st->getId(config.getName()));
    if (!config.isUsed()) {
      Error err(ErrorDefinition::ELAB_CONFIGURATION_IGNORED, loc);
      m_compileDesign->getCompiler()->getErrorContainer()->addError(err);
      unused.emplace_back(name);
    } else {
      Error err(ErrorDefinition::ELAB_CONFIGURATION_USED, loc);
      m_compileDesign->getCompiler()->getErrorContainer()->addError(err);
    }
  }

  // Remove unused configs from set
  for (const auto& name : unused) {
    std::vector<Config>::iterator itr;
    for (itr = allConfigs.begin(); itr != allConfigs.end(); itr++) {
      if ((*itr).getName() == name) {
        allConfigs.erase(itr);
        break;
      }
    }
  }

  // Create top level module list and recurse configs
  for (auto& config : allConfigs) {
    if (config.isTopLevel()) {
      const std::string_view lib = config.getDesignLib();
      const std::string_view top = config.getDesignTop();
      std::string name = StrCat(lib, "@", top);
      m_toplevelConfigModules.insert(name);
      m_instConfig.emplace(name, config);
      m_cellConfig.emplace(name, config);

      for (auto& instClause : config.getInstanceUseClauses()) {
        m_instUseClause.emplace(StrCat(lib, "@", instClause.first),
                                instClause.second);
        if (instClause.second.getType() == UseClause::UseConfig) {
          Config* config =
              configSet->getMutableConfigByName(instClause.second.getName());
          if (config) {
            std::set<Config*> configStack;
            recurseBuildInstanceClause_(StrCat(lib, "@", instClause.first),
                                        config, configStack);
          }
        }
      }
      for (auto& cellClause : config.getCellUseClauses()) {
        m_cellUseClause.emplace(cellClause.first, cellClause.second);
      }
    }
  }
  return true;
}

void DesignElaboration::recurseBuildInstanceClause_(
    std::string_view parentPath, Config* config,
    std::set<Config*>& configStack) {
  if (configStack.find(config) != configStack.end()) {
    return;
  }
  configStack.insert(config);

  ConfigSet* configSet =
      m_compileDesign->getCompiler()->getDesign()->getConfigSet();
  for (auto& useClause : config->getInstanceUseClauses()) {
    std::string inst = useClause.first;
    std::string fullPath = StrCat(parentPath, ".", inst);
    m_instUseClause.emplace(fullPath, useClause.second);
    if (useClause.second.getType() == UseClause::UseConfig) {
      Config* config =
          configSet->getMutableConfigByName(useClause.second.getName());
      if (config) {
        recurseBuildInstanceClause_(StrCat(parentPath, ".", useClause.first),
                                    config, configStack);
      }
    }
  }
  for (auto& useClause : config->getCellUseClauses()) {
    std::string inst = useClause.first;
    std::string fullPath = inst;
    m_cellUseClause.emplace(fullPath, useClause.second);
  }
}

bool DesignElaboration::identifyTopModules_() {
  FileSystem* const fileSystem = FileSystem::getInstance();
  m_topLevelModules.clear();
  bool modulePresent = false;
  bool toplevelModuleFound = false;
  SymbolTable* st = m_compileDesign->getCompiler()->getSymbolTable();
  auto& userTopList = m_compileDesign->getCompiler()
                          ->getCommandLineParser()
                          ->getTopLevelModules();
  auto all_files =
      m_compileDesign->getCompiler()->getDesign()->getAllFileContents();
  typedef std::multimap<std::string,
                        std::pair<const DesignElement*, const FileContent*>>
      ModuleMultiMap;
  ModuleMultiMap all_modules;
  for (auto file : all_files) {
    if (m_compileDesign->getCompiler()->isLibraryFile(file.first)) continue;
    for (const DesignElement* element : file.second->getDesignElements()) {
      const std::string_view elemName = st->getSymbol(element->m_name);
      if (element->m_type == DesignElement::Module) {
        if (element->m_parent) {
          // This is a nested element
          continue;
        }
        const std::string_view libName = file.second->getLibrary()->getName();
        std::string topname = StrCat(libName, "@", elemName);

        if (!file.second->getParent()) {
          // Files that have parent are splited files (When a module is too
          // large it is splited)
          all_modules.emplace(topname, std::make_pair(element, file.second));
        }

        modulePresent = true;
        bool used = false;
        for (auto file1 : all_files) {
          if (file1.second->getReferencedObjects().find(elemName) !=
              file1.second->getReferencedObjects().end()) {
            if (m_compileDesign->getCompiler()->isLibraryFile(file1.first))
              continue;
            used = true;
            break;
          }
        }

        if (!used) {
          bool isTop = true;

          if (!m_toplevelConfigModules.empty()) {
            isTop = false;
            if (m_toplevelConfigModules.find(topname) !=
                m_toplevelConfigModules.end()) {
              isTop = true;
            }
          }

          if (isTop) {
            SymbolId topid = st->registerSymbol(topname);
            auto itr = m_uniqueTopLevelModules.find(topname);
            Location loc(file.second->getFileId(element->m_node),
                         element->m_line, element->m_column, topid);
            if (itr == m_uniqueTopLevelModules.end()) {
              bool okModule = true;
              if (!userTopList.empty()) {
                if (userTopList.find(elemName) == userTopList.end())
                  okModule = false;
              }
              if (okModule) {
                m_uniqueTopLevelModules.insert(topname);
                m_topLevelModules.emplace_back(topname, file.second);
                toplevelModuleFound = true;
                Error err(ErrorDefinition::ELAB_TOP_LEVEL_MODULE, loc);
                m_compileDesign->getCompiler()->getErrorContainer()->addError(
                    err);
              }
            }
          }
        }
      }
    }
  }

  // Check for multiple definition
  std::string prevModuleName;
  const DesignElement* prevModuleDefinition = nullptr;
  const FileContent* prevFileContent = nullptr;
  for (ModuleMultiMap::iterator itr = all_modules.begin();
       itr != all_modules.end(); itr++) {
    std::string moduleName = (*itr).first;
    const DesignElement* moduleDefinition = (*itr).second.first;
    const FileContent* fileContent = (*itr).second.second;
    bool done = false;
    if (moduleName == prevModuleName) {
      const FileContent* fC1 = (*itr).second.second;
      NodeId nodeId1 = moduleDefinition->m_node;
      PathId fileId1 = fileSystem->copy(fC1->getFileId(nodeId1), st);
      uint32_t line1 = fC1->Line(nodeId1);
      Location loc1(fileId1, line1, fC1->Column(nodeId1),
                    st->registerSymbol(moduleName));

      std::vector<Location> locations;

      while (true) {
        const FileContent* fC2 = prevFileContent;
        NodeId nodeId2 = prevModuleDefinition->m_node;
        PathId fileId2 = fileSystem->copy(fC2->getFileId(nodeId2), st);
        uint32_t line2 = fC2->Line(nodeId2);
        Location loc2(fileId2, line2, fC2->Column(nodeId2),
                      st->registerSymbol(moduleName));

        if ((fileId1 != fileId2) || (line1 != line2)) {
          locations.push_back(loc2);
        }

        itr++;
        if (itr == all_modules.end()) {
          done = true;
          break;
        } else {
          std::string nextModuleName = (*itr).first;
          const DesignElement* nextModuleDefinition = (*itr).second.first;
          const FileContent* nextFileContent = (*itr).second.second;
          prevModuleName = nextModuleName;
          prevModuleDefinition = nextModuleDefinition;
          prevFileContent = nextFileContent;
          if (prevModuleName != moduleName) {
            moduleName = prevModuleName;
            moduleDefinition = prevModuleDefinition;
            fileContent = prevFileContent;
            break;
          }
        }
      }

      if (!locations.empty()) {
        Error err1(ErrorDefinition::ELAB_MULTIPLY_DEFINED_MODULE, loc1,
                   &locations);
        m_compileDesign->getCompiler()->getErrorContainer()->addError(err1);
      }
    }
    prevModuleName = moduleName;
    prevModuleDefinition = moduleDefinition;
    prevFileContent = fileContent;
    if (done) break;
  }

  if (m_topLevelModules.size() > 1) {
    Location loc(BadSymbolId);
    Error err(ErrorDefinition::ELAB_MULTIPLE_TOP_LEVEL_MODULES, loc);
    m_compileDesign->getCompiler()->getErrorContainer()->addError(err);
  }

  // User overrides
  if (!toplevelModuleFound) {
    for (const auto& userM : userTopList) {
      bool found = false;
      for (auto file : all_files) {
        if (m_compileDesign->getCompiler()->isLibraryFile(file.first)) continue;
        for (const DesignElement* element : file.second->getDesignElements()) {
          const std::string_view elemName = st->getSymbol(element->m_name);
          if (element->m_type == DesignElement::Module) {
            if (element->m_parent) {
              // This is a nested element
              continue;
            }
            if (userM != elemName) {
              continue;
            }
            found = true;
            Location locUser(st->registerSymbol(userM));
            Error errUser(ErrorDefinition::ELAB_TOP_LEVEL_IS_NOT_A_TOP_LEVEL,
                          locUser);
            m_compileDesign->getCompiler()->getErrorContainer()->addError(
                errUser);

            const std::string_view libName =
                file.second->getLibrary()->getName();
            std::string topname = StrCat(libName, "@", elemName);
            m_uniqueTopLevelModules.insert(topname);
            m_topLevelModules.emplace_back(topname, file.second);
            toplevelModuleFound = true;
            SymbolId topid = st->registerSymbol(topname);
            Location loc(file.second->getFileId(element->m_node),
                         element->m_line, element->m_column, topid);
            Error err(ErrorDefinition::ELAB_TOP_LEVEL_MODULE, loc);
            m_compileDesign->getCompiler()->getErrorContainer()->addError(err);
          }
        }
      }
      if (!found) {
        Location locUser(st->registerSymbol(userM));
        Error errUser(ErrorDefinition::ELAB_TOP_LEVEL_DOES_NOT_EXIST, locUser);
        m_compileDesign->getCompiler()->getErrorContainer()->addError(errUser);
      }
    }
  }

  if (modulePresent && (!toplevelModuleFound)) {
    Location loc(BadSymbolId);
    Error err(ErrorDefinition::ELAB_NO_TOP_LEVEL_MODULE, loc);
    m_compileDesign->getCompiler()->getErrorContainer()->addError(err);
  }

  return true;
}

bool DesignElaboration::createBuiltinPrimitives_() {
  m_moduleDefFactory = new ModuleDefinitionFactory();
  Design* design = m_compileDesign->getCompiler()->getDesign();

  // Register built-in primitives
  for (auto type : {"cmos",     "rcmos",    "bufif0",
                    "bufif1",   "notif0",   "notif1",
                    "nmos",     "pmos",     "rnmos",
                    "rpmos",    "and",      "or",
                    "nand",     "nor",      "xor",
                    "xnor",     "buf",      "not",
                    "tranif0",  "tranif1",  "rtranif0",
                    "rtranif1", "tran",     "rtran",
                    "pullup",   "pulldown", "UnsupportedPrimitive"}) {
    std::string name = std::string("work@") + type;
    design->addModuleDefinition(
        name, m_moduleDefFactory->newModuleDefinition(
                  nullptr, InvalidNodeId, std::string("work@") + type));
  }

  return true;
}

bool DesignElaboration::elaborateAllModules_(bool onlyTopLevel) {
  bool status = true;
  for (const auto& topmodule : m_topLevelModules) {
    if (!elaborateModule_(topmodule.first, topmodule.second, onlyTopLevel)) {
      status = false;
    }
  }
  return status;
}

Config* DesignElaboration::getInstConfig(std::string_view name) {
  Config* config = nullptr;
  auto itr = m_instConfig.find(name);
  if (itr != m_instConfig.end()) {
    config = &(*itr).second;
  }
  return config;
}

Config* DesignElaboration::getCellConfig(std::string_view name) {
  Config* config = nullptr;
  auto itr = m_cellConfig.find(name);
  if (itr != m_cellConfig.end()) {
    config = &(*itr).second;
  }
  return config;
}

bool DesignElaboration::bindAllInstances_(ModuleInstance* parent,
                                          ModuleInstanceFactory* factory,
                                          Config* config) {
  DesignComponent* def = parent->getDefinition();
  Design* design = m_compileDesign->getCompiler()->getDesign();
  std::vector<ModuleInstance*> parentSubInstances;
  if (def) {
    for (BindStmt* bind : design->getBindStmts(def->getName())) {
      ModuleInstance* bindInstance =
          createBindInstance_(bind, parent, factory, config);
      if (bindInstance) {
        parentSubInstances.push_back(bindInstance);
      }
    }
  }
  for (uint32_t i = 0; i < parent->getNbChildren(); i++) {
    ModuleInstance* child = parent->getChildren(i);
    bindAllInstances_(child, factory, config);
  }
  for (auto inst : parentSubInstances) {
    parent->addSubInstance(inst);
  }
  return true;
}

bool DesignElaboration::elaborateModule_(std::string_view moduleName,
                                         const FileContent* fC,
                                         bool onlyTopLevel) {
  const FileContent::NameIdMap& nameIds = fC->getObjectLookup();
  const std::string_view libName = fC->getLibrary()->getName();
  Config* config = getInstConfig(moduleName);
  if (config == nullptr) config = getCellConfig(moduleName);
  Design* design = m_compileDesign->getCompiler()->getDesign();
  if (!m_moduleInstFactory) m_moduleInstFactory = new ModuleInstanceFactory();
  for (const auto& nameId : nameIds) {
    if ((fC->Type(nameId.second) == VObjectType::paModule_declaration) &&
        (moduleName == StrCat(libName, "@", nameId.first))) {
      DesignComponent* def = design->getComponentDefinition(moduleName);
      if (onlyTopLevel) {
        ModuleInstance* instance = m_moduleInstFactory->newModuleInstance(
            def, fC, nameId.second, nullptr, moduleName, moduleName);
        design->addTopLevelModuleInstance(instance);
      } else {
        ModuleInstance* instance = design->findInstance(moduleName);
        for (uint32_t i = 0; i < def->getFileContents().size(); i++) {
          std::vector<ModuleInstance*> parentSubInstances;
          NodeId id = def->getNodeIds()[i];
          elaborateInstance_(def->getFileContents()[i], id, InvalidNodeId,
                             m_moduleInstFactory, instance, config,
                             parentSubInstances);
          if (instance)
            bindAllInstances_(instance, m_moduleInstFactory, config);
        }
      }
      break;
    }
  }
  return true;
}

void DesignElaboration::recurseInstanceLoop_(
    std::vector<int32_t>& from, std::vector<int32_t>& to,
    std::vector<int32_t>& indexes, uint32_t pos, DesignComponent* def,
    const FileContent* fC, NodeId subInstanceId, NodeId paramOverride,
    ModuleInstanceFactory* factory, ModuleInstance* parent, Config* config,
    std::string instanceName, std::string_view modName,
    std::vector<ModuleInstance*>& allSubInstances) {
  if (pos == indexes.size()) {
    // This is where the real logic goes.
    // indexes[i] contain the value of the i-th index.
    for (int32_t index : indexes) {
      if (!instanceName.empty()) {
        if (instanceName[instanceName.size() - 1] == ' ') {
          instanceName.erase(instanceName.end() - 1);
        }
      }
      StrAppend(&instanceName, "[", index, "]");
    }
    ModuleInstance* child = factory->newModuleInstance(
        def, fC, subInstanceId, parent, instanceName, modName);
    VObjectType type = fC->Type(subInstanceId);
    if (def && (type != VObjectType::paGate_instantiation)) {
      for (uint32_t i = 0; i < def->getFileContents().size(); i++) {
        elaborateInstance_(def->getFileContents()[i], def->getNodeIds()[i],
                           paramOverride, factory, child, config,
                           allSubInstances);
      }
    }
    allSubInstances.push_back(child);

  } else {
    for (indexes[pos] = from[pos]; indexes[pos] <= to[pos]; indexes[pos]++) {
      // Recurse for the next level
      recurseInstanceLoop_(from, to, indexes, pos + 1, def, fC, subInstanceId,
                           paramOverride, factory, parent, config, instanceName,
                           modName, allSubInstances);
    }
  }
}

ModuleInstance* DesignElaboration::createBindInstance_(
    BindStmt* bind, ModuleInstance* parent, ModuleInstanceFactory* factory,
    Config* config) {
  ModuleInstance* instance = nullptr;
  const FileContent* fC = bind->getFileContent();
  Library* lib = fC->getLibrary();
  NodeId bindNodeId = bind->getBindId();
  const std::string bindModName =
      StrCat(lib->getName(), "@", fC->SymName(bindNodeId));
  NodeId instNameId = bind->getInstanceId();
  const std::string_view instName = fC->SymName(instNameId);
  NodeId targetModId = bind->getTargetModId();
  NodeId targetInstId = bind->getTargetInstId();
  const std::string targetName =
      StrCat(lib->getName(), "@", fC->SymName(targetModId));
  DesignComponent* def = parent->getDefinition();
  Design* design = m_compileDesign->getCompiler()->getDesign();
  bool instanceMatch = true;
  if (targetInstId) {
    const std::string_view targetInstName = fC->SymName(targetInstId);
    instanceMatch = (targetInstName == parent->getInstanceName());
  }
  DesignComponent* targetDef = nullptr;
  if (def && (def->getName() == targetName) && instanceMatch) {
    targetDef = design->getModuleDefinition(bindModName);
    if (targetDef) {
      instance = factory->newModuleInstance(targetDef, fC, bind->getStmtId(),
                                            parent->getParent(), instName,
                                            bindModName);
    } else {
      SymbolTable* st =
          m_compileDesign->getCompiler()->getErrorContainer()->getSymbolTable();
      Location loc(fC->getFileId(bind->getStmtId()),
                   fC->Line(bind->getStmtId()), fC->Column(bind->getStmtId()),
                   st->registerSymbol(bindModName));
      Error err(ErrorDefinition::ELAB_NO_MODULE_DEFINITION, loc);
      m_compileDesign->getCompiler()->getErrorContainer()->addError(err, false,
                                                                    false);
    }
  }
  if (instance) {
    std::vector<ModuleInstance*> parentSubInstances;
    instance->setInstanceBinding(parent);
    if (instance->getParent() == nullptr) {
      instance->setParent(parent);
    }
    NodeId parameterOverloading = fC->Sibling(bindNodeId);
    if (fC->Type(parameterOverloading) ==
        VObjectType::paHierarchical_instance) {
      parameterOverloading = InvalidNodeId;
    }
    elaborateInstance_(targetDef->getFileContents()[0],
                       targetDef->getNodeIds()[0], parameterOverloading,
                       factory, instance, config, parentSubInstances);
  }
  return instance;
}

const UHDM::any* resize(UHDM::Serializer& serializer, const UHDM::any* object,
                        int32_t maxsize, bool is_overall_unsigned) {
  if (object == nullptr) {
    return nullptr;
  }
  UHDM::any* result = (UHDM::any*)object;
  UHDM::UHDM_OBJECT_TYPE type = result->UhdmType();
  if (type == UHDM::uhdmconstant) {
    UHDM::constant* c = (UHDM::constant*)result;
    if (c->VpiSize() < maxsize) {
      UHDM::ElaboratorContext elaboratorContext(&serializer);
      c = (UHDM::constant*)UHDM::clone_tree(c, &elaboratorContext);
      int32_t constType = c->VpiConstType();
      const UHDM::typespec* tps = nullptr;
      if (const UHDM::ref_typespec* rt = c->Typespec()) {
        tps = rt->Actual_typespec();
      }
      bool is_signed = false;
      if (tps) {
        if (tps->UhdmType() == UHDM::uhdmint_typespec) {
          UHDM::int_typespec* itps = (UHDM::int_typespec*)tps;
          if (itps->VpiSigned()) {
            is_signed = true;
          }
        }
      }
      if (constType == vpiBinaryConst) {
        std::string value(c->VpiValue());
        if (is_signed && (!is_overall_unsigned)) {
          value.insert(4, (maxsize - c->VpiSize()), '1');
        } else {
          value.insert(4, (maxsize - c->VpiSize()), '0');
        }
        c->VpiValue(value);
      }
      c->VpiSize(maxsize);
      result = c;
    }
  }
  return result;
}

void DesignElaboration::elaborateInstance_(
    const FileContent* fC, NodeId nodeId, NodeId parentParamOverride,
    ModuleInstanceFactory* factory, ModuleInstance* parent, Config* config,
    std::vector<ModuleInstance*>& parentSubInstances) {
  if (!parent) return;
  // Turn to true to debug instance parameters
  bool debugInstParam = false;

  CommandLineParser* clp =
      m_compileDesign->getCompiler()->getCommandLineParser();
  auto& blackboxModules = clp->getBlackBoxModules();
  std::string modName;
  if (DesignComponent* def = parent->getDefinition()) {
    modName = def->getName();
  }
  if (blackboxModules.find(modName) != blackboxModules.end()) {
    SymbolTable* st =
        m_compileDesign->getCompiler()->getErrorContainer()->getSymbolTable();
    Location loc(fC->getFileId(), fC->Line(nodeId), fC->Column(nodeId),
                 st->registerSymbol(modName));
    Error err(ErrorDefinition::ELAB_SKIPPING_BLACKBOX_MODULE, loc);
    m_compileDesign->getCompiler()->getErrorContainer()->addError(err, false,
                                                                  false);
    return;
  }
  auto& blackboxInstances = clp->getBlackBoxInstances();
  std::string instanceName;
  if (parent) {
    instanceName = parent->getFullPathName();
  }
  if (blackboxInstances.find(modName) != blackboxInstances.end()) {
    SymbolTable* st =
        m_compileDesign->getCompiler()->getErrorContainer()->getSymbolTable();
    Location loc(fC->getFileId(), fC->Line(nodeId), fC->Column(nodeId),
                 st->registerSymbol(modName));
    Error err(ErrorDefinition::ELAB_SKIPPING_BLACKBOX_INSTANCE, loc);
    m_compileDesign->getCompiler()->getErrorContainer()->addError(err, false,
                                                                  false);
    return;
  }
  if (blackboxInstances.find(instanceName) != blackboxInstances.end()) {
    SymbolTable* st =
        m_compileDesign->getCompiler()->getErrorContainer()->getSymbolTable();
    Location loc(fC->getFileId(), fC->Line(nodeId), fC->Column(nodeId),
                 st->registerSymbol(instanceName));
    Error err(ErrorDefinition::ELAB_SKIPPING_BLACKBOX_INSTANCE, loc);
    m_compileDesign->getCompiler()->getErrorContainer()->addError(err, false,
                                                                  false);
    return;
  }

  std::vector<ModuleInstance*>& allSubInstances = parent->getAllSubInstances();
  std::string genBlkBaseName = "genblk";
  uint32_t genBlkIndex = 1;
  bool reuseInstance = false;
  std::string mname;

  // Scan for parameters, including DefParams
  std::vector<std::string_view> params =
      collectParams_(fC, nodeId, parent, parentParamOverride);

  // Loop checking
  bool loopDetected = false;
  ModuleInstance* tmp = parent;
  DesignComponent* parentDef = tmp->getDefinition();
  if (tmp) {
    tmp = tmp->getParent();
  }
  while (tmp) {
    if (tmp->getDefinition() == parentDef) {
      loopDetected = true;
      for (const auto& pvalues : parent->getMappedValues()) {
        const std::string& name = pvalues.first;
        Value* pval = pvalues.second.first;
        Value* val = tmp->getValue(name, m_exprBuilder);
        if (val) {
          if (*pval != *val) {
            loopDetected = false;
            break;
          }
        }
      }
      for (const auto& cvalues : parent->getComplexValues()) {
        const std::string& name = cvalues.first;
        UHDM::expr* pval = cvalues.second;
        UHDM::expr* val = tmp->getComplexValue(name);
        if (val) {
          if (pval != val) {
            loopDetected = false;
            break;
          }
        }
      }
      break;
    }
    tmp = tmp->getParent();
  }
  if (loopDetected) {
    SymbolTable* st =
        m_compileDesign->getCompiler()->getErrorContainer()->getSymbolTable();
    Location loc(fC->getFileId(parent->getNodeId()),
                 fC->Line(parent->getNodeId()), fC->Column(parent->getNodeId()),
                 st->registerSymbol(parent->getModuleName()));
    Location loc2(tmp->getFileContent()->getFileId(tmp->getNodeId()),
                  tmp->getFileContent()->Line(tmp->getNodeId()),
                  tmp->getFileContent()->Column(tmp->getNodeId()));
    Error err(ErrorDefinition::ELAB_INSTANTIATION_LOOP, loc, loc2);
    m_compileDesign->getCompiler()->getErrorContainer()->addError(err);
    return;
  }

  // Apply DefParams
  Design* design = m_compileDesign->getCompiler()->getDesign();
  for (const auto& name : params) {
    DefParam* defparam =
        design->getDefParam(StrCat(parent->getFullPathName(), ".", name));
    if (defparam) {
      Value* value = defparam->getValue();
      if (value) {
        parent->setValue(name, value, m_exprBuilder);
        defparam->setUsed();
      }
    }
  }
  bindDataTypes_(parent, parent->getDefinition());

  // Scan for regular instances and generate blocks
  VObjectTypeUnorderedSet types = {
      VObjectType::paUdp_instantiation, VObjectType::paModule_instantiation,
      VObjectType::paInterface_instantiation,
      VObjectType::paProgram_instantiation, VObjectType::paGate_instantiation,
      VObjectType::paConditional_generate_construct,  // Generate construct are
                                                      // a kind of instantiation
      VObjectType::paGenerate_module_conditional_statement,
      VObjectType::paGenerate_interface_conditional_statement,
      VObjectType::paLoop_generate_construct,
      VObjectType::paGenerate_module_loop_statement,
      VObjectType::paGenerate_interface_loop_statement,
      VObjectType::paPar_block, VObjectType::paSeq_block,
      VObjectType::paGenerate_region, VObjectType::paGenerate_begin_end_block};

  VObjectTypeUnorderedSet stopPoints = {
      VObjectType::paConditional_generate_construct,
      VObjectType::paGenerate_module_conditional_statement,
      VObjectType::paGenerate_interface_conditional_statement,
      VObjectType::paLoop_generate_construct,
      VObjectType::paGenerate_module_loop_statement,
      VObjectType::paGenerate_interface_loop_statement,
      VObjectType::paPar_block,
      VObjectType::paSeq_block,
      VObjectType::paModule_declaration,
      VObjectType::paBind_directive,
      VObjectType::paGenerate_region,
      VObjectType::paGenerate_begin_end_block,
      VObjectType::paFunction_declaration,
      VObjectType::paTask_declaration};

  std::vector<NodeId> subInstances =
      fC->sl_collect_all(nodeId, types, stopPoints);
  for (auto subInstanceId : subInstances) {
    VObjectType type = fC->Type(subInstanceId);
    std::vector<NodeId> subSubInstances;
    std::string instName;
    if (type == VObjectType::paGenerate_region) {
      NodeId Generate_item = fC->Child(subInstanceId);
      if (fC->Type(Generate_item) != VObjectType::paGenerate_item) {
        continue;
      }
      NodeId nameId = fC->Child(Generate_item);
      if (fC->Name(nameId)) {
        instName = fC->SymName(nameId);
        subSubInstances.push_back(subInstanceId);
      } else {
        while (Generate_item) {
          std::vector<NodeId> subIds =
              fC->sl_collect_all(Generate_item, types, stopPoints);
          if (!subIds.empty()) {
            for (auto id : subIds) {
              subSubInstances.push_back(id);
            }
          } else {
            if (DesignComponent* def = parent->getDefinition()) {
              // Compile generate block
              ((ModuleDefinition*)def)->setGenBlockId(Generate_item);
              FunctorCompileModule funct(
                  m_compileDesign, (ModuleDefinition*)def, design,
                  m_compileDesign->getCompiler()->getSymbolTable(),
                  m_compileDesign->getCompiler()->getErrorContainer(), parent);
              funct.operator()();
            }
          }
          Generate_item = fC->Sibling(Generate_item);
          if (Generate_item &&
              (fC->Type(Generate_item) == VObjectType::paENDGENERATE)) {
            break;
          }
        }
      }
    } else {
      subSubInstances.push_back(subInstanceId);
    }
  }

  NetlistElaboration* nelab = new NetlistElaboration(m_compileDesign);
  nelab->elaborateInstance(parent);
  delete nelab;

  for (auto subInstanceId : subInstances) {
    VObjectType type = fC->Type(subInstanceId);
    std::vector<NodeId> subSubInstances;
    std::string instName;
    if (type == VObjectType::paGenerate_region) {
      NodeId Generate_item = fC->Child(subInstanceId);
      if (fC->Type(Generate_item) != VObjectType::paGenerate_item) {
        continue;
      }
      NodeId nameId = fC->Child(Generate_item);
      if (fC->Name(nameId)) {
        instName = fC->SymName(nameId);
        subSubInstances.push_back(subInstanceId);
      } else {
        while (Generate_item) {
          std::vector<NodeId> subIds =
              fC->sl_collect_all(Generate_item, types, stopPoints);
          if (!subIds.empty()) {
            for (auto id : subIds) {
              subSubInstances.push_back(id);
            }
          } else {
          }
          Generate_item = fC->Sibling(Generate_item);
          if (Generate_item &&
              (fC->Type(Generate_item) == VObjectType::paENDGENERATE)) {
            break;
          }
        }
      }
    } else {
      subSubInstances.push_back(subInstanceId);
    }

    for (auto subInstanceId : subSubInstances) {
      NodeId childId;
      std::string modName;
      DesignComponent* def = nullptr;
      ModuleInstance* child = nullptr;
      NodeId paramOverride;
      Config* subConfig = config;
      VObjectType type = fC->Type(subInstanceId);

      if (type == VObjectType::paSeq_block ||
          type == VObjectType::paPar_block) {
        NodeId identifierId = fC->Child(subInstanceId);
        if (fC->Name(identifierId))
          instName = fC->SymName(identifierId);
        else {
          instName = genBlkBaseName + std::to_string(genBlkIndex);
          genBlkIndex++;
        }
      } else if (type == VObjectType::paConditional_generate_construct) {
        NodeId constructId = fC->Child(subInstanceId);
        NodeId condId = fC->Child(constructId);
        NodeId blockId = fC->Sibling(condId);
        NodeId nameId = fC->Child(blockId);
        if (fC->Name(nameId))
          instName = fC->SymName(nameId);
        else {
          instName = genBlkBaseName + std::to_string(genBlkIndex);
        }
      } else {
        NodeId instId =
            fC->sl_collect(subInstanceId, VObjectType::paName_of_instance);
        if (instId == InvalidNodeId) {
          NodeId nameId = fC->Child(subInstanceId);
          if (fC->Type(nameId) == VObjectType::slStringConst) {
            instId = subInstanceId;
          }
        }
        NodeId identifierId;
        if (instId) {
          identifierId = fC->Child(instId);
          instName = fC->SymName(identifierId);
        }
      }

      // Special module binding for built-in primitives
      if (type == VObjectType::paGate_instantiation) {
        VObjectType gatetype = fC->Type(fC->Child(subInstanceId));
        modName = UhdmWriter::builtinGateName(gatetype);
        def = design->getComponentDefinition(modName);
        NodeId instanceId = fC->Sibling(fC->Child(subInstanceId));
        while (instanceId) {
          NodeId instId =
              fC->sl_collect(instanceId, VObjectType::paName_of_instance);
          NodeId identifierId;
          if (instId) {
            identifierId = fC->Child(instId);
            instName = fC->SymName(identifierId);
          }
          child = factory->newModuleInstance(def, fC, instanceId, parent,
                                             instName, modName);
          parent->addSubInstance(child);
          bindDataTypes_(parent, def);
          NetlistElaboration* nelab = new NetlistElaboration(m_compileDesign);
          nelab->elaborateInstance(child);
          delete nelab;
          instanceId = fC->Sibling(instanceId);
        }
      }
      // Special module binding for generate statements
      else if (type == VObjectType::paConditional_generate_construct ||
               type == VObjectType::paGenerate_module_conditional_statement ||
               type ==
                   VObjectType::paGenerate_interface_conditional_statement ||
               type == VObjectType::paLoop_generate_construct ||
               type == VObjectType::paGenerate_module_loop_statement ||
               type == VObjectType::paGenerate_interface_loop_statement) {
        modName = genBlkBaseName + std::to_string(genBlkIndex);
        std::string append = "0";
        while (parent->getValue(modName, m_exprBuilder)) {
          modName = genBlkBaseName + append + std::to_string(genBlkIndex);
          append += "0";
        }
        VObjectTypeUnorderedSet btypes = {
            VObjectType::paGenerate_module_block,
            VObjectType::paGenerate_interface_block,
            VObjectType::paGenerate_begin_end_block,
            VObjectType::paGenerate_module_named_block,
            VObjectType::paGenerate_interface_named_block};

        std::vector<NodeId> blockIds;
        genBlkIndex++;
        instName = modName;
        std::string fullName;
        std::string_view libName = fC->getLibrary()->getName();
        if (instName == parent->getInstanceName()) {
          fullName += parent->getFullPathName();
          reuseInstance = true;
        } else {
          StrAppend(&fullName, parent->getModuleName(), ".", instName);
        }

        NodeId conditionId = fC->Child(subInstanceId);
        if (fC->Type(conditionId) == VObjectType::paIf_generate_construct) {
          NodeId IF = fC->Child(conditionId);
          conditionId = fC->Sibling(IF);
        }
        VObjectType conditionType = fC->Type(conditionId);
        if (conditionType == VObjectType::paGenvar_initialization ||
            conditionType ==
                VObjectType::paGenvar_decl_assignment) {  // For loop stmt

          // Var init
          NodeId varId = fC->Child(conditionId);
          NodeId constExpr = fC->Sibling(varId);

          bool validValue;
          m_helper.checkForLoops(true);
          uint64_t initVal = (uint64_t)m_helper.getValue(
              validValue, parentDef, fC, constExpr, m_compileDesign,
              Reduce::Yes, nullptr, parent, false);
          m_helper.checkForLoops(false);
          Value* initValue = m_exprBuilder.getValueFactory().newLValue();
          initValue->set(initVal);

          const std::string_view name = fC->SymName(varId);
          parent->setValue(name, initValue, m_exprBuilder, fC->Line(varId));

          // End-loop test
          NodeId endLoopTest = fC->Sibling(conditionId);

          // Iteration
          NodeId iteration = fC->Sibling(endLoopTest);
          NodeId var = fC->Child(iteration);
          NodeId assignOp = fC->Sibling(var);
          NodeId expr = fC->Sibling(assignOp);
          if (!expr) {  // Unary operator like i++
            expr = var;
          } else if (fC->Type(assignOp) !=
                     VObjectType::paAssignOp_Assign) {  // Operators like +=
            expr = var;
          }
          // Generate block
          NodeId genBlock = fC->Sibling(iteration);
          if (fC->Type(fC->Child(genBlock)) ==
              VObjectType::paGenerate_begin_end_block)
            genBlock = fC->Child(genBlock);
          m_helper.checkForLoops(true);
          int64_t condVal = m_helper.getValue(
              validValue, parentDef, fC, endLoopTest, m_compileDesign,
              Reduce::Yes, nullptr, parent, false);
          m_helper.checkForLoops(false);
          bool cont = (validValue && (condVal > 0));

          NodeId blockNameId = fC->Child(genBlock);
          if (fC->Type(blockNameId) == VObjectType::slStringConst) {
            modName = fC->SymName(blockNameId);
          }
          while (cont) {
            Value* currentIndexValue = parent->getValue(name, m_exprBuilder);
            uint64_t currVal = currentIndexValue->getValueUL();
            std::string indexedModName = parent->getFullPathName() + "." +
                                         modName + "[" +
                                         std::to_string(currVal) + "]";
            instName = modName + "[" + std::to_string(currVal) + "]";

            def = design->getComponentDefinition(indexedModName);
            if (def == nullptr) {
              def = m_moduleDefFactory->newModuleDefinition(fC, genBlock,
                                                            indexedModName);
              if (DesignComponent* defParent = parent->getDefinition())
                def->setParentScope(defParent);
              design->addModuleDefinition(indexedModName,
                                          (ModuleDefinition*)def);
            }

            // Compile generate block
            ((ModuleDefinition*)def)->setGenBlockId(genBlock);
            FunctorCompileModule funct(
                m_compileDesign, (ModuleDefinition*)def, design,
                m_compileDesign->getCompiler()->getSymbolTable(),
                m_compileDesign->getCompiler()->getErrorContainer(), parent);
            funct.operator()();

            child = factory->newModuleInstance(def, fC, genBlock, parent,
                                               instName, indexedModName);
            child->setValue(name, m_exprBuilder.clone(currentIndexValue),
                            m_exprBuilder, fC->Line(varId));
            elaborateInstance_(def->getFileContents()[0], genBlock,
                               InvalidNodeId, factory, child, config,
                               allSubInstances);
            parent->addSubInstance(child);

            // First try the simple expression evaluator (handles i = i + 1, etc.)
            Value* newVal = m_exprBuilder.evalExpr(fC, expr, parent);
            if (!newVal->isValid()) {
              // Fallback: use full expression compilation for complex increments
              // like step = step * CHUNK (where CHUNK is a parameter)
              m_helper.checkForLoops(true);
              int64_t newValInt = m_helper.getValue(
                  validValue, parentDef, fC, expr, m_compileDesign, Reduce::Yes,
                  nullptr, parent, false);
              m_helper.checkForLoops(false);
              if (validValue) {
                newVal->set((uint64_t)newValInt);
              }
            }
            parent->setValue(name, newVal, m_exprBuilder, fC->Line(varId));
            m_helper.checkForLoops(true);
            condVal = m_helper.getValue(validValue, parentDef, fC, endLoopTest,
                                        m_compileDesign, Reduce::Yes, nullptr,
                                        parent, false);
            m_helper.checkForLoops(false);
            cont = (validValue && (condVal > 0));

            if (!newVal->isValid()) {
              cont = false;
            }
          }
          parent->deleteValue(name, m_exprBuilder);
          continue;

        } else {  // If-Else or Case stmt
          if (fC->Type(conditionId) != VObjectType::paConstant_expression) {
            conditionId = fC->Child(conditionId);
          }
          bool validValue;
          m_helper.checkForLoops(true);
          int64_t condVal = m_helper.getValue(
              validValue, parentDef, fC, conditionId, m_compileDesign,
              Reduce::Yes, nullptr, parent, false);
          m_helper.checkForLoops(false);
          NodeId tmp = fC->Sibling(conditionId);

          if (fC->Type(tmp) ==
              VObjectType::paCase_generate_item) {  // Case stmt
            // Make all expressions match the largest expression size per LRM
            int32_t maxsize = 0;
            bool is_overall_unsigned = false;
            {
              std::vector<NodeId> checkIds;
              checkIds.push_back(conditionId);
              NodeId caseItem = tmp;
              while (caseItem) {
                NodeId exprItem = fC->Child(caseItem);
                while (exprItem) {
                  if (fC->Type(exprItem) ==
                      VObjectType::paConstant_expression) {
                    checkIds.push_back(exprItem);
                  }
                  exprItem = fC->Sibling(exprItem);
                }
                caseItem = fC->Sibling(caseItem);
              }

              for (NodeId id : checkIds) {
                m_helper.checkForLoops(true);
                UHDM::any* tmpExp = m_helper.compileExpression(
                    parentDef, fC, id, m_compileDesign, Reduce::Yes, nullptr,
                    parent, false);
                m_helper.checkForLoops(false);
                if (tmpExp && (tmpExp->UhdmType() == UHDM::uhdmconstant)) {
                  UHDM::constant* c = (UHDM::constant*)tmpExp;
                  maxsize = std::max(maxsize, c->VpiSize());
                  const UHDM::typespec* tps = nullptr;
                  if (const UHDM::ref_typespec* rt = c->Typespec()) {
                    tps = rt->Actual_typespec();
                  }
                  bool is_signed = false;
                  if (tps) {
                    if (tps->UhdmType() == UHDM::uhdmint_typespec) {
                      UHDM::int_typespec* itps = (UHDM::int_typespec*)tps;
                      if (itps->VpiSigned()) {
                        is_signed = true;
                      }
                    }
                  }
                  if (is_signed == false) {
                    is_overall_unsigned = true;
                  }
                }
              }
            }
            m_helper.checkForLoops(true);
            const UHDM::any* condExpr = m_helper.compileExpression(
                parentDef, fC, conditionId, m_compileDesign, Reduce::Yes,
                nullptr, parent, false);
            m_helper.checkForLoops(false);
            condExpr = resize(m_compileDesign->getSerializer(), condExpr,
                              maxsize, is_overall_unsigned);
            UHDM::ExprEval eval;
            bool invalidValue = false;
            condVal = eval.get_value(
                invalidValue, any_cast<const UHDM::expr*>(condExpr), true);
            if (invalidValue) {
              Location loc(fC->getFileId(conditionId), fC->Line(conditionId),
                           fC->Column(conditionId));
              Error err(ErrorDefinition::ELAB_INVALID_CASE_STMT_VALUE, loc);
              m_compileDesign->getCompiler()->getErrorContainer()->addError(
                  err, false, false);
            }
            NodeId caseItem = tmp;
            bool nomatch = true;
            while (nomatch) {
              NodeId exprItem = fC->Child(caseItem);
              if (fC->Type(exprItem) ==
                  VObjectType::paGenerate_item)  // Default block
                nomatch = false;
              while (nomatch) {
                // Find if one of the case expr matches the case expr
                if (fC->Type(exprItem) == VObjectType::paConstant_expression) {
                  m_helper.checkForLoops(true);
                  const UHDM::any* caseExpr = m_helper.compileExpression(
                      parentDef, fC, exprItem, m_compileDesign, Reduce::Yes,
                      nullptr, parent, false);
                  m_helper.checkForLoops(false);
                  caseExpr = resize(m_compileDesign->getSerializer(), caseExpr,
                                    maxsize, is_overall_unsigned);
                  UHDM::ExprEval eval;
                  bool invalidValue = false;
                  int64_t caseVal = eval.get_value(
                      invalidValue, any_cast<const UHDM::expr*>(caseExpr),
                      true);
                  if (invalidValue) {
                    Location loc(fC->getFileId(exprItem), fC->Line(exprItem),
                                 fC->Column(exprItem));
                    Error err(ErrorDefinition::ELAB_INVALID_CASE_STMT_VALUE,
                              loc);
                    m_compileDesign->getCompiler()
                        ->getErrorContainer()
                        ->addError(err, false, false);
                  }
                  if (condVal == caseVal) {
                    nomatch = false;
                    break;
                  }
                } else
                  break;
                exprItem = fC->Sibling(exprItem);
              }

              if (nomatch) {
                // Next case stmt
                caseItem = fC->Sibling(caseItem);
                if (!caseItem) break;
                if (fC->Type(caseItem) != VObjectType::paCase_generate_item)
                  break;
              } else {
                // We found a match
                while (fC->Type(exprItem) == VObjectType::paConstant_expression)
                  exprItem = fC->Sibling(exprItem);
                childId = exprItem;
              }
            }
          } else {              // If-Else stmt
            if (condVal > 0) {  // If branch
              if (tmp)
                childId = tmp;
              else  // There is no If stmt
                continue;
            } else {  // Else branch
              if (!tmp) continue;
              bool activeBranch = false;
              while (true) {
                if (tmp) {
                  tmp = fC->Sibling(tmp);  // Else
                  if (!tmp) break;
                  tmp = fC->Sibling(tmp);
                  int64_t condVal = 0;

                  NodeId Generate_item = tmp;
                  NodeId Generate_begin_end_block = fC->Child(Generate_item);
                  NodeId Module_or_generate_item;
                  if (fC->Type(Generate_begin_end_block) ==
                      VObjectType::paModule_or_generate_item) {
                    Module_or_generate_item = Generate_begin_end_block;
                  } else {
                    Module_or_generate_item =
                        fC->Child(Generate_begin_end_block);
                  }
                  if (fC->Type(Module_or_generate_item) ==
                      VObjectType::slStringConst) {
                    Generate_item = fC->Sibling(Module_or_generate_item);
                    Module_or_generate_item = fC->Child(Generate_item);
                  }
                  NodeId Cond;
                  if (fC->Type(Module_or_generate_item) ==
                      VObjectType::paModule_or_generate_item) {
                    NodeId Module_common_item =
                        fC->Child(Module_or_generate_item);
                    NodeId Conditional_generate_construct =
                        fC->Child(Module_common_item);
                    NodeId If_generate_construct =
                        fC->Child(Conditional_generate_construct);
                    Cond = fC->Child(If_generate_construct);
                    if (fC->Type(Cond) == VObjectType::paIF) {
                      Cond = fC->Sibling(Cond);
                    }
                    if (fC->Type(Cond) == VObjectType::paConstant_expression) {
                      bool validValue;
                      m_helper.checkForLoops(true);
                      condVal = m_helper.getValue(
                          validValue, parentDef, fC, Cond, m_compileDesign,
                          Reduce::Yes, nullptr, parent, false);
                      m_helper.checkForLoops(false);
                    } else {
                      // It is not an else-if
                      condVal = true;
                    }
                  } else if (fC->Type(Generate_item) ==
                             VObjectType::
                                 paGenerate_module_conditional_statement) {
                    Cond = fC->Child(Generate_item);
                    if (fC->Type(Cond) == VObjectType::paIF) {
                      Cond = fC->Sibling(Cond);
                    }
                    if (fC->Type(Cond) == VObjectType::paConstant_expression) {
                      bool validValue;
                      m_helper.checkForLoops(true);
                      condVal = m_helper.getValue(
                          validValue, parentDef, fC, Cond, m_compileDesign,
                          Reduce::Yes, nullptr, parent, false);
                      m_helper.checkForLoops(false);
                    } else {
                      // It is not an else-if
                      condVal = true;
                    }

                  } else {
                    // It is not an else-if
                    condVal = true;
                  }

                  if (condVal > 0) {
                    activeBranch = true;
                    childId = tmp;
                    break;
                  } else {
                    // Else branch
                    tmp = fC->Sibling(Cond);
                  }

                } else {  // There is no Else stmt
                  activeBranch = false;
                  break;
                }
              }
              if (!activeBranch) continue;

              // refresh instName
              NodeId blockNameId = fC->Child(tmp);
              if (fC->Type(blockNameId) == VObjectType::slStringConst ||
                  fC->Type(blockNameId) ==
                      VObjectType::paGenerate_begin_end_block) {  // if-else
                if (fC->Type(blockNameId) ==
                    VObjectType::paGenerate_begin_end_block) {
                  NodeId Identifier = fC->Child(blockNameId);
                  NodeId Generate_item = Identifier;
                  if (fC->Type(Identifier) == VObjectType::slStringConst) {
                    Generate_item = fC->Sibling(Identifier);
                    modName = fC->SymName(Identifier);
                  }
                  NodeId Module_or_generate_item = fC->Child(Generate_item);
                  NodeId Module_common_item =
                      fC->Child(Module_or_generate_item);
                  NodeId Conditional_generate_construct =
                      fC->Child(Module_common_item);
                  NodeId If_generate_construct =
                      fC->Child(Conditional_generate_construct);
                  if (fC->Type(If_generate_construct) ==
                      VObjectType::paIf_generate_construct) {
                    if (fC->Type(childId) == VObjectType::paGenerate_item)
                      childId = fC->Child(childId);
                    blockIds = fC->sl_collect_all(childId, btypes, true);
                    if (!blockIds.empty()) {
                      NodeId blockId = blockIds[0];
                      NodeId blockNameId = fC->Child(blockId);
                      if (fC->Type(blockNameId) == VObjectType::slStringConst) {
                        modName = fC->SymName(blockNameId);
                        subInstanceId = fC->Sibling(blockNameId);
                        childId = subInstanceId;
                      } else {
                        subInstanceId = childId;
                      }
                    }
                  } else {
                    subInstanceId = tmp;
                    childId = subInstanceId;
                  }
                } else {
                  modName = fC->SymName(blockNameId);
                  subInstanceId = tmp;
                  childId = subInstanceId;
                }

              } else {  // if-else-if
                blockIds = fC->sl_collect_all(childId, btypes, true);
                if (!blockIds.empty()) {
                  NodeId blockId = blockIds[0];
                  NodeId blockNameId = fC->Child(blockId);
                  if (fC->Type(blockNameId) == VObjectType::slStringConst) {
                    modName = fC->SymName(blockNameId);
                    subInstanceId = fC->Sibling(blockNameId);
                    childId = subInstanceId;
                  } else {
                    subInstanceId = childId;
                  }
                }
              }
              instName = modName;
            }
          }
        }

        libName = fC->getLibrary()->getName();
        NodeId blockId = childId;
        if (fC->Type(fC->Child(blockId)) ==
            VObjectType::paGenerate_begin_end_block) {
          blockId = fC->Child(blockId);
        }
        if (fC->Type(blockId) == VObjectType::paGenerate_begin_end_block &&
            (fC->Type(fC->Child(blockId)) != VObjectType::slStringConst))
          blockId = fC->Child(blockId);
        NodeId blockNameId = fC->Child(blockId);
        if (fC->Type(blockNameId) == VObjectType::slStringConst) {
          modName = fC->SymName(blockNameId);
          instName = modName;
        }
        std::string indexedModName = parent->getFullPathName() + "." + modName;
        def = design->getComponentDefinition(indexedModName);
        if (def == nullptr) {
          def = m_moduleDefFactory->newModuleDefinition(fC, blockId,
                                                        indexedModName);
          if (DesignComponent* defParent = parent->getDefinition())
            def->setParentScope(defParent);
          design->addModuleDefinition(indexedModName, (ModuleDefinition*)def);
        }

        if (debugInstParam) {
          fullName = std::string(parent->getModuleName()) + std::string(".") +
                     instName;

          std::cout << "Inst:" << fullName << ", modName:" << modName
                    << std::endl;
          for (auto param : parent->getMappedValues()) {
            std::cout << param.first << " " << param.second.first->uhdmValue()
                      << std::endl;
          }
          for (auto& param : parent->getComplexValues()) {
            std::cout << param.first << std::endl;
            UHDM::decompile(param.second);
            std::cout << std::endl;
          }
        }

        // Compile generate block
        ((ModuleDefinition*)def)->setGenBlockId(blockId);
        FunctorCompileModule funct(
            m_compileDesign, (ModuleDefinition*)def, design,
            m_compileDesign->getCompiler()->getSymbolTable(),
            m_compileDesign->getCompiler()->getErrorContainer(), parent);
        funct.operator()();

        child = factory->newModuleInstance(def, fC, blockId, parent, instName,
                                           indexedModName);
        while (blockId) {
          elaborateInstance_(def->getFileContents()[0], blockId, paramOverride,
                             factory, child, config, allSubInstances);
          blockId = fC->Sibling(blockId);
          if (fC->Type(blockId) == VObjectType::paGenerate_begin_end_block) {
            NodeId subChild = fC->Child(blockId);
            if (fC->Type(subChild) == VObjectType::paGenerate_begin_end_block) {
              break;
            }
          }
          if (fC->Type(blockId) == VObjectType::paGenerate_module_item) {
            NodeId node = fC->Child(blockId);
            if (fC->Type(node) ==
                VObjectType::paGenerate_module_conditional_statement) {
              break;
            }
            if (fC->Type(node) == VObjectType::paGenerate_module_block) {
              break;
            }
          }
          if (fC->Type(blockId) == VObjectType::paELSE) break;
          if (fC->Type(blockId) == VObjectType::paEND) break;
        }
        parent->addSubInstance(child);
      }
      // Named blocks
      else if (type == VObjectType::paSeq_block ||
               type == VObjectType::paPar_block) {
        std::string fullName = StrCat(parent->getModuleName(), ".", instName);

        def = design->getComponentDefinition(fullName);
        if (def == nullptr) {
          def = m_moduleDefFactory->newModuleDefinition(fC, subInstanceId,
                                                        fullName);
          design->addModuleDefinition(fullName, (ModuleDefinition*)def);
        }

        ModuleInstance* child = factory->newModuleInstance(
            def, fC, subInstanceId, parent, instName, modName);
        elaborateInstance_(def->getFileContents()[0], subInstanceId,
                           paramOverride, factory, child, config,
                           allSubInstances);
        parent->addSubInstance(child);

      } else if (type == VObjectType::paGenerate_region) {
        NodeId Generate_begin_end_block = fC->Child(subInstanceId);
        if (fC->Type(Generate_begin_end_block) !=
            VObjectType::paGenerate_begin_end_block) {
          continue;
        }
        NodeId nameId = fC->Child(Generate_begin_end_block);
        if (fC->Name(nameId)) {
          instName = fC->SymName(nameId);
        }

        std::string fullName;
        if (instName.empty())
          fullName = StrCat(parent->getModuleName(), ".", genBlkBaseName,
                            std::to_string(genBlkIndex));
        else
          fullName = StrCat(parent->getModuleName(), ".", instName);

        def = design->getComponentDefinition(fullName);
        NodeId childId = fC->Child(subInstanceId);
        if (def == nullptr) {
          def = m_moduleDefFactory->newModuleDefinition(fC, subInstanceId,
                                                        fullName);
          design->addModuleDefinition(fullName, (ModuleDefinition*)def);
        }

        if (instName.empty()) {
          instName = genBlkBaseName + std::to_string(genBlkIndex);
        } else {
          // Compile generate block
          ((ModuleDefinition*)def)->setGenBlockId(childId);
          FunctorCompileModule funct(
              m_compileDesign, (ModuleDefinition*)def, design,
              m_compileDesign->getCompiler()->getSymbolTable(),
              m_compileDesign->getCompiler()->getErrorContainer(), parent);
          funct.operator()();
        }

        ModuleInstance* child = factory->newModuleInstance(
            def, fC, subInstanceId, parent, instName, modName);
        elaborateInstance_(def->getFileContents()[0], subInstanceId,
                           paramOverride, factory, child, config,
                           allSubInstances);
        parent->addSubInstance(child);
      } else if (type == VObjectType::paGenerate_begin_end_block) {
        NodeId nameId = fC->Child(subInstanceId);
        if (fC->Name(nameId)) {
          instName = fC->SymName(nameId);
        }

        std::string fullName;
        if (instName.empty())
          fullName = StrCat(parent->getModuleName(), ".", genBlkBaseName,
                            std::to_string(genBlkIndex));
        else
          fullName = StrCat(parent->getModuleName(), ".", instName);

        def = design->getComponentDefinition(fullName);
        NodeId childId = fC->Child(subInstanceId);
        if (def == nullptr) {
          def = m_moduleDefFactory->newModuleDefinition(fC, subInstanceId,
                                                        fullName);
          design->addModuleDefinition(fullName, (ModuleDefinition*)def);
        }

        if (instName.empty()) {
          instName = genBlkBaseName + std::to_string(genBlkIndex);
        } else {
          // Compile generate block
          ((ModuleDefinition*)def)->setGenBlockId(childId);
          FunctorCompileModule funct(
              m_compileDesign, (ModuleDefinition*)def, design,
              m_compileDesign->getCompiler()->getSymbolTable(),
              m_compileDesign->getCompiler()->getErrorContainer(), parent);
          funct.operator()();
        }

        ModuleInstance* child = factory->newModuleInstance(
            def, fC, subInstanceId, parent, instName, modName);
        elaborateInstance_(def->getFileContents()[0], subInstanceId,
                           paramOverride, factory, child, config,
                           allSubInstances);
        parent->addSubInstance(child);
      } else {
        // Regular module binding
        NodeId moduleName =
            fC->sl_collect(subInstanceId, VObjectType::slStringConst);
        const std::string_view libName = fC->getLibrary()->getName();
        mname = fC->SymName(moduleName);

        if (debugInstParam) {
          std::string fullName = std::string(parent->getModuleName()) +
                                 std::string(".") + instName;

          std::cout << "Inst:" << fullName << ", modName:" << modName
                    << std::endl;
          for (auto param : parent->getMappedValues()) {
            std::cout << param.first << " " << param.second.first->uhdmValue()
                      << std::endl;
          }
          for (auto& param : parent->getComplexValues()) {
            std::cout << param.first << std::endl;
            UHDM::decompile(param.second);
            std::cout << std::endl;
          }
        }

        std::vector<std::string> libs;
        if (config) {
          const auto& defaultLibs = config->getDefaultLibs();
          libs.insert(libs.end(), defaultLibs.begin(), defaultLibs.end());
        }
        libs.emplace_back(libName);

        for (const auto& lib : libs) {
          modName = StrCat(lib, "@", mname);
          def = design->getComponentDefinition(modName);
          if (def) {
            break;
          } else {
            modName.assign(parent->getDefinition()->getName())
                .append("::")
                .append(mname);
            def = design->getComponentDefinition(modName);
            if (def) {
              break;
            }
          }
        }

        auto itr = m_cellUseClause.find(mname);
        if (itr != m_cellUseClause.end()) {
          UseClause& use = (*itr).second;
          switch (use.getType()) {
            case UseClause::UseModule: {
              const std::string_view name = use.getName();
              def = design->getComponentDefinition(name);
              if (def) use.setUsed();
              break;
            }
            case UseClause::UseLib: {
              for (const auto& lib : use.getLibs()) {
                modName = StrCat(lib, "@", mname);
                def = design->getComponentDefinition(modName);
                if (def) {
                  use.setUsed();
                  break;
                }
              }
              break;
            }
            default:
              break;
          }
        }

        if (def) childId = def->getNodeIds()[0];

        NodeId tmpId = fC->Sibling(moduleName);
        VObjectType tmpType = fC->Type(tmpId);
        if (tmpType == VObjectType::paParameter_value_assignment ||
            tmpType == VObjectType::paDelay2 ||
            tmpType == VObjectType::slIntConst) {
          paramOverride = tmpId;
        }

        VObjectTypeUnorderedSet insttypes = {
            VObjectType::paHierarchical_instance,
            VObjectType::paN_input_gate_instance,
            VObjectType::paN_output_gate_instance,
            VObjectType::paPull_gate_instance, VObjectType::paUdp_instance};

        std::vector<NodeId> hierInstIds =
            fC->sl_collect_all(subInstanceId, insttypes, true);

        NodeId hierInstId;
        if (!hierInstIds.empty()) hierInstId = hierInstIds[0];

        if (!hierInstId) continue;

        while (hierInstId) {
          NodeId instId =
              fC->sl_collect(hierInstId, VObjectType::paName_of_instance);
          NodeId identifierId;
          if (instId) {
            identifierId = fC->Child(instId);
            instName = fC->SymName(identifierId);
          }

          auto itr =
              m_instUseClause.find(parent->getFullPathName() + "." + instName);
          if (itr != m_instUseClause.end()) {
            UseClause& use = (*itr).second;
            switch (use.getType()) {
              case UseClause::UseModule: {
                const std::string_view name = use.getName();
                def = design->getComponentDefinition(name);
                if (def) use.setUsed();
                break;
              }
              case UseClause::UseLib: {
                const auto& libs = use.getLibs();
                if (!libs.empty()) {
                  const auto& lib = libs.front();
                  modName = StrCat(lib, "@", mname);
                  def = design->getComponentDefinition(modName);
                  if (def) {
                    use.setUsed();
                  }
                }
                break;
              }
              case UseClause::UseConfig: {
                const std::string_view useConfig = use.getName();
                Config* config =
                    design->getConfigSet()->getMutableConfigByName(useConfig);
                if (config) {
                  subConfig = config;
                  const std::string_view lib = config->getDesignLib();
                  const std::string_view top = config->getDesignTop();
                  modName = StrCat(lib, "@", top);
                  def = design->getComponentDefinition(modName);
                  if (def) use.setUsed();
                }
                break;
              }
              default:
                break;
            }
          }

          if (def)
            childId = def->getNodeIds()[0];
          else {
            SymbolTable* st = m_compileDesign->getCompiler()
                                  ->getErrorContainer()
                                  ->getSymbolTable();
            Location loc(fC->getFileId(subInstanceId), fC->Line(subInstanceId),
                         fC->Column(subInstanceId),
                         st->registerSymbol(modName));
            Error err(ErrorDefinition::ELAB_NO_MODULE_DEFINITION, loc);
            m_compileDesign->getCompiler()->getErrorContainer()->addError(
                err, false, false);
          }

          NodeId unpackedDimId;
          if (identifierId) unpackedDimId = fC->Sibling(identifierId);

          if (unpackedDimId) {
            std::vector<int32_t> from;
            std::vector<int32_t> to;
            std::vector<int32_t> index;

            // Vector instances
            while (unpackedDimId) {
              if (fC->Type(unpackedDimId) ==
                  VObjectType::paUnpacked_dimension) {
                NodeId constantRangeId = fC->Child(unpackedDimId);
                NodeId leftNode = fC->Child(constantRangeId);
                NodeId rightNode = fC->Sibling(leftNode);
                bool validValue;
                m_helper.checkForLoops(true);
                int64_t left = m_helper.getValue(
                    validValue, parentDef, fC, leftNode, m_compileDesign,
                    Reduce::Yes, nullptr, parent, false);
                m_helper.checkForLoops(false);
                int64_t right = 0;
                if (rightNode && (fC->Type(rightNode) ==
                                  VObjectType::paConstant_expression)) {
                  m_helper.checkForLoops(true);
                  right = m_helper.getValue(
                      validValue, parentDef, fC, rightNode, m_compileDesign,
                      Reduce::Yes, nullptr, parent, false);
                  m_helper.checkForLoops(false);
                }
                if (left < right) {
                  from.push_back(left);
                  to.push_back(right);
                  index.push_back(left);
                } else {
                  from.push_back(right);
                  to.push_back(left);
                  index.push_back(right);
                }
              }
              unpackedDimId = fC->Sibling(unpackedDimId);
            }

            std::vector<ModuleInstance*> localSubInstances;
            recurseInstanceLoop_(from, to, index, 0, def, fC, subInstanceId,
                                 paramOverride, factory, parent, subConfig,
                                 instName, modName, localSubInstances);
            allSubInstances.insert(allSubInstances.end(),
                                   localSubInstances.begin(),
                                   localSubInstances.end());

            // Create module array
            if (type == VObjectType::paModule_instantiation) {
              int32_t unpackedSize = 0;
              unpackedDimId = fC->Sibling(identifierId);
              if (std::vector<UHDM::range*>* unpackedDimensions =
                      m_helper.compileRanges(
                          def, fC, unpackedDimId, m_compileDesign, Reduce::No,
                          nullptr, parent, unpackedSize, false)) {
                UHDM::Serializer& s = m_compileDesign->getSerializer();
                UHDM::module_array* mod_array = s.MakeModule_array();
                mod_array->Ranges(unpackedDimensions);
                mod_array->VpiName(instName);
                mod_array->VpiFullName(modName);
                fC->populateCoreMembers(identifierId, identifierId, mod_array);

                UHDM::module_typespec* tps = s.MakeModule_typespec();
                NodeId typespecId = fC->Child(subInstanceId);
                tps->VpiName(fC->SymName(typespecId));
                fC->populateCoreMembers(typespecId, typespecId, tps);
                UHDM::ref_typespec* tpsRef = s.MakeRef_typespec();
                tpsRef->VpiParent(mod_array);
                tpsRef->Actual_typespec(tps);
                mod_array->Elem_typespec(tpsRef);
                parent->getModuleArrayModuleInstancesMap().emplace(
                    mod_array, localSubInstances);
              }
            }
          } else {
            // Simple instance
            if (reuseInstance) {
              child = parent;
              child->setNodeId(subInstanceId);
            } else {
              child = factory->newModuleInstance(def, fC, subInstanceId, parent,
                                                 instName, modName);
            }
            if (def && (type != VObjectType::paGate_instantiation)) {
              elaborateInstance_(def->getFileContents()[0], childId,
                                 paramOverride, factory, child, subConfig,
                                 allSubInstances);
            } else {
              // Build black box model
              std::vector<std::string_view> params =
                  collectParams_(fC, subInstanceId, child, paramOverride);
              NetlistElaboration* nelab =
                  new NetlistElaboration(m_compileDesign);
              nelab->elaborateInstance(child);
              delete nelab;
            }
            if (!reuseInstance) parent->addSubInstance(child);
          }

          hierInstId = fC->Sibling(hierInstId);
        }
        // std::cout << "INST: " << modName << " " << instName << " " << def <<
        // std::endl;
      }
    }
  }
}

void DesignElaboration::reportElaboration_() {
  uint32_t nbTopLevelModules = 0;
  uint32_t maxDepth = 0;
  uint32_t numberOfInstances = 0;
  uint32_t numberOfLeafInstances = 0;
  uint32_t nbUndefinedModules = 0;
  uint32_t nbUndefinedInstances = 0;

  m_compileDesign->getCompiler()->getDesign()->reportInstanceTreeStats(
      nbTopLevelModules, maxDepth, numberOfInstances, numberOfLeafInstances,
      nbUndefinedModules, nbUndefinedInstances);

  SymbolTable* symtable = m_compileDesign->getCompiler()->getSymbolTable();

  Location loc1(symtable->registerSymbol(std::to_string(nbTopLevelModules)));
  Error err1(ErrorDefinition::ELAB_NB_TOP_LEVEL_MODULES, loc1);
  m_compileDesign->getCompiler()->getErrorContainer()->addError(err1);

  Location loc2(symtable->registerSymbol(std::to_string(maxDepth)));
  Error err2(ErrorDefinition::ELAB_MAX_INSTANCE_DEPTH, loc2);
  m_compileDesign->getCompiler()->getErrorContainer()->addError(err2);

  Location loc3(symtable->registerSymbol(std::to_string(numberOfInstances)));
  Error err3(ErrorDefinition::ELAB_NB_INSTANCES, loc3);
  m_compileDesign->getCompiler()->getErrorContainer()->addError(err3);

  Location loc4(
      symtable->registerSymbol(std::to_string(numberOfLeafInstances)));
  Error err4(ErrorDefinition::ELAB_NB_LEAF_INSTANCES, loc4);
  m_compileDesign->getCompiler()->getErrorContainer()->addError(err4);

  if (nbUndefinedModules) {
    Location loc5(symtable->registerSymbol(std::to_string(nbUndefinedModules)));
    Error err5(ErrorDefinition::ELAB_NB_UNDEF_MODULES, loc5);
    m_compileDesign->getCompiler()->getErrorContainer()->addError(err5);
  }

  if (nbUndefinedInstances) {
    Location loc6(
        symtable->registerSymbol(std::to_string(nbUndefinedInstances)));
    Error err6(ErrorDefinition::ELAB_NB_UNDEF_INSTANCES, loc6);
    m_compileDesign->getCompiler()->getErrorContainer()->addError(err6);
  }
  CommandLineParser* cl =
      m_compileDesign->getCompiler()->getCommandLineParser();
  if (cl->getDebugInstanceTree() && (!cl->muteStdout())) {
    std::cout << "Instance tree:" << std::endl;
    std::cout
        << m_compileDesign->getCompiler()->getDesign()->reportInstanceTree();
    std::cout << std::endl;
  }
}

std::vector<std::string_view> DesignElaboration::collectParams_(
    const FileContent* fC, NodeId nodeId, ModuleInstance* instance,
    NodeId parentParamOverride) {
  std::vector<std::string_view> params;
  if (!nodeId) return params;
  if (!instance) return params;
  bool en_replay =
      m_compileDesign->getCompiler()->getCommandLineParser()->replay();
  Design* design = m_compileDesign->getCompiler()->getDesign();
  SymbolTable* st = m_compileDesign->getCompiler()->getSymbolTable();
  ErrorContainer* errors = m_compileDesign->getCompiler()->getErrorContainer();
  DesignComponent* module = instance->getDefinition();
  // Parameters imported by package imports
  std::vector<FileCNodeId> pack_imports;
  for (const auto& import :
       fC->getObjects(VObjectType::paPackage_import_item)) {
    pack_imports.push_back(import);
  }
  if (module) {
    for (auto import : module->getObjects(VObjectType::paPackage_import_item)) {
      pack_imports.push_back(import);
    }
  }
  for (const auto& pack_import : pack_imports) {
    NodeId pack_id = pack_import.fC->Child(pack_import.nodeId);
    const std::string_view pack_name = pack_import.fC->SymName(pack_id);
    Package* def = design->getPackage(pack_name);
    if (def) {
      auto& paramSet = def->getObjects(VObjectType::paParam_assignment);
      for (const auto& element : paramSet) {
        const FileContent* packageFile = element.fC;
        NodeId param = element.nodeId;

        NodeId ident = packageFile->Child(param);
        const std::string_view name = packageFile->SymName(ident);
        if (UHDM::expr* exp = def->getComplexValue(name)) {
          UHDM::Serializer& s = m_compileDesign->getSerializer();
          UHDM::ElaboratorContext elaboratorContext(&s, false, true);
          UHDM::any* pclone = UHDM::clone_tree(exp, &elaboratorContext);
          instance->setComplexValue(name, (UHDM::expr*)pclone);
        } else {
          Value* value = m_exprBuilder.clone(def->getValue(name));
          if (value)
            instance->setValue(name, value, m_exprBuilder,
                               packageFile->Line(param));
        }
        params.emplace_back(name);
      }
    } else {
      Location loc(
          pack_import.fC->getFileId(pack_id), pack_import.fC->Line(pack_id),
          pack_import.fC->Column(pack_id), st->registerSymbol(pack_name));
      Error err(ErrorDefinition::ELAB_UNDEFINED_PACKAGE, loc);
      errors->addError(err);
    }
  }

  std::vector<std::string_view> moduleParams;
  if (module) {
    for (FileCNodeId param :
         module->getObjects(VObjectType::paParam_assignment)) {
      NodeId ident = param.fC->Child(param.nodeId);
      const std::string_view name = param.fC->SymName(ident);
      params.emplace_back(name);
      moduleParams.emplace_back(name);
    }
  }
  std::set<std::string_view> overridenParams;
  // Param overrides
  if (parentParamOverride) {
    ModuleInstance* parentInstance = instance->getParent();
    DesignComponent* parentDefinition =
        (instance->getParent()) ? instance->getParent()->getDefinition()
                                : instance->getDefinition();
    if (instance->getInstanceBinding()) {
      parentInstance = instance->getInstanceBinding();
      parentDefinition = parentInstance->getDefinition();
    }
    const FileContent* parentFile =
        instance->getParent()->getDefinition()->getFileContents()[0];
    VObjectTypeUnorderedSet types = {
        VObjectType::paOrdered_parameter_assignment,
        VObjectType::paNamed_parameter_assignment};
    std::vector<NodeId> overrideParams =
        parentFile->sl_collect_all(parentParamOverride, types);
    if (parentFile->Type(parentParamOverride) == VObjectType::paDelay2) {
      NodeId tmp = parentFile->Child(parentParamOverride);
      if (parentFile->Type(tmp) == VObjectType::paMintypmax_expression) {
        while (tmp) {
          overrideParams.push_back(tmp);
          tmp = parentFile->Sibling(tmp);
        }
      } else {
        overrideParams.push_back(parentParamOverride);
      }
    } else if (parentFile->Type(parentParamOverride) ==
               VObjectType::slIntConst) {
      // dffr #4 u1 ( )
      overrideParams.push_back(parentParamOverride);
    }
    uint32_t index = 0;
    for (auto paramAssign : overrideParams) {
      NodeId child = parentFile->Child(paramAssign);
      if (parentFile->Type(paramAssign) == VObjectType::paDelay2 ||
          parentFile->Type(paramAssign) == VObjectType::slIntConst) {
        child = paramAssign;
      }
      if (parentFile->Type(child) == VObjectType::slStringConst) {
        // Named param
        const std::string_view name = parentFile->SymName(child);
        overridenParams.insert(name);
        if (module) {
          Parameter* p = module->getParameter(name);
          if (p == nullptr) {
            Location loc(parentFile->getFileId(paramAssign),
                         parentFile->Line(paramAssign),
                         parentFile->Column(paramAssign),
                         st->registerSymbol(name));
            Error err(ErrorDefinition::ELAB_UNKNOWN_PARAMETER_OVERRIDE, loc);
            errors->addError(err);
            continue;
          }
        }
        NodeId expr = parentFile->Sibling(child);
        if (!expr) {
          Location loc(
              parentFile->getFileId(paramAssign), parentFile->Line(paramAssign),
              parentFile->Column(paramAssign), st->registerSymbol(name));
          Error err(ErrorDefinition::ELAB_EMPTY_PARAM_OVERRIDE, loc);
          errors->addError(err);
          continue;
        }
        m_helper.checkForLoops(true);
        UHDM::expr* complexV = (UHDM::expr*)m_helper.compileExpression(
            parentDefinition, parentFile, expr, m_compileDesign, Reduce::Yes,
            nullptr, parentInstance, false);
        m_helper.checkForLoops(false);
        Value* value = nullptr;
        bool complex = false;
        if (complexV) {
          UHDM::UHDM_OBJECT_TYPE exprtype = complexV->UhdmType();
          if (exprtype == UHDM::uhdmconstant) {
            UHDM::constant* c = (UHDM::constant*)complexV;
            if (en_replay && m_helper.errorOnNegativeConstant(
                                 parentDefinition, complexV, m_compileDesign,
                                 parentInstance)) {
              bool replay = false;
              // GDB: p replay=true
              if (replay) {
                m_helper.compileExpression(parentDefinition, parentFile, expr,
                                           m_compileDesign, Reduce::Yes,
                                           nullptr, parentInstance, false);

                m_exprBuilder.evalExpr(parentFile, expr, parentInstance, true);
              }
            }
            const std::string_view v = c->VpiValue();
            value = m_exprBuilder.fromVpiValue(v, c->VpiSize());
          } else if ((exprtype == UHDM::uhdmoperation) ||
                     (exprtype == UHDM::uhdmfunc_call) ||
                     (exprtype == UHDM::uhdmsys_func_call) ||
                     (exprtype == UHDM::uhdmindexed_part_select) ||
                     (exprtype == UHDM::uhdmhier_path)) {
            if (instance) {
              complex = true;
              if (m_helper.substituteAssignedValue(complexV, m_compileDesign)) {
                instance->setComplexValue(name, complexV);
                instance->setOverridenParam(name);
              } else {
                m_helper.checkForLoops(true);
                complexV = (UHDM::expr*)m_helper.compileExpression(
                    parentDefinition, parentFile, expr, m_compileDesign,
                    Reduce::No, nullptr, parentInstance, false);
                m_helper.checkForLoops(false);
                if (complexV->UhdmType() == UHDM::uhdmref_obj) {
                  UHDM::ref_obj* ref = (UHDM::ref_obj*)complexV;
                  if (ref->Actual_group() == nullptr) {
                    ref->Actual_group(m_helper.bindParameter(
                        parentDefinition, parentInstance, ref->VpiName(),
                        m_compileDesign, true));
                  }
                }
                instance->setComplexValue(name, complexV);
                instance->setOverridenParam(name);
              }
            }
          } else if (exprtype == UHDM::uhdmref_obj) {
            bool isTypeParam = false;
            if (module) {
              Parameter* p = module->getParameter(name);
              if (p) isTypeParam = p->isTypeParam();
            }
            if (!isTypeParam) {
              complex = true;
              UHDM::ref_obj* ref = (UHDM::ref_obj*)complexV;
              if (ref->Actual_group() == nullptr) {
                ref->Actual_group(m_helper.bindParameter(
                    parentDefinition, parentInstance, ref->VpiName(),
                    m_compileDesign, true));
              }
              instance->setComplexValue(name, complexV);
              instance->setOverridenParam(name);
            }
          } else if (exprtype == UHDM::uhdmparameter) {
            UHDM::parameter* param = (UHDM::parameter*)complexV;
            const std::string_view pname = param->VpiName();
            const UHDM::typespec* tps = nullptr;
            if (const UHDM::ref_typespec* rt = param->Typespec()) {
              tps = rt->Actual_typespec();
            }
            const UHDM::instance* pinst = tps->Instance();
            if (pinst->UhdmType() == UHDM::uhdmpackage) {
              Design* design = m_compileDesign->getCompiler()->getDesign();
              if (Package* pack = design->getPackage(pinst->VpiName())) {
                if ((complexV = pack->getComplexValue(pname))) {
                  complex = true;
                  instance->setComplexValue(name, complexV);
                  instance->setOverridenParam(name);
                }
                if (complexV == nullptr) {
                  if ((value = pack->getValue(pname))) {
                    instance->setValue(name, value, m_exprBuilder,
                                       parentFile->Line(expr));
                    instance->setOverridenParam(name);
                  }
                }
              }
            } else if (ValuedComponentI* parent = instance->getParent()) {
              complexV = parent->getComplexValue(pname);
              if (complexV) {
                complex = true;
                instance->setComplexValue(name, complexV);
                instance->setOverridenParam(name);
              } else if ((value = parent->getValue(pname, m_exprBuilder))) {
                instance->setValue(name, value, m_exprBuilder,
                                   parentFile->Line(expr));
                instance->setOverridenParam(name);
              }
            }
          }
        }
        if (complex == false) {
          if (value == nullptr) {
            if (module) {
              Parameter* p = module->getParameter(name);
              bool isTypeParam = false;
              if (p) isTypeParam = p->isTypeParam();
              value = m_exprBuilder.evalExpr(parentFile, expr, parentInstance,
                                             isTypeParam);
              if (en_replay && m_helper.errorOnNegativeConstant(
                                   parentDefinition, value, m_compileDesign,
                                   parentInstance)) {
                bool replay = false;
                // GDB: p replay=true
                if (replay) {
                  m_exprBuilder.evalExpr(parentFile, expr, parentInstance,
                                         isTypeParam);
                }
              }
            }
          }
          if (value == nullptr || (value && !value->isValid())) {
            bool replay = false;
            // GDB: p replay=true
            if (replay) {
              m_helper.compileExpression(parentDefinition, parentFile, expr,
                                         m_compileDesign, Reduce::Yes, nullptr,
                                         parentInstance, false);
            }

            const std::string_view pname = parentFile->SymName(child);
            NodeId param_expression = parentFile->Sibling(child);
            NodeId data_type = parentFile->Child(param_expression);
            NodeId type = parentFile->Child(data_type);
            Parameter* param =
                new Parameter(parentFile, expr, pname, type, true);
            instance->getTypeParams().push_back(param);
            // Set the invalid value as a marker for netlist elaboration
            instance->setValue(name, value, m_exprBuilder,
                               parentFile->Line(expr));
            instance->setOverridenParam(name);
          } else {
            instance->setValue(name, value, m_exprBuilder,
                               parentFile->Line(expr));
            instance->setOverridenParam(name);
          }
        }
      } else if (module) {
        // Index param
        NodeId expr = child;
        const DesignComponent::ParameterVec& params =
            module->getOrderedParameters();
        Parameter* p = nullptr;
        bool isTypeParam = false;
        if (index < params.size()) {
          p = params.at(index);
          isTypeParam = p->isTypeParam();
        }
        m_helper.checkForLoops(true);
        UHDM::expr* complexV = (UHDM::expr*)m_helper.compileExpression(
            parentDefinition, parentFile, expr, m_compileDesign, Reduce::Yes,
            nullptr, parentInstance, false);
        m_helper.checkForLoops(false);
        Value* value = nullptr;
        bool complex = false;

        static constexpr std::string_view kOutOfRangeParamIndex =
            "OUT_OF_RANGE_PARAM_INDEX";
        std::string_view name = kOutOfRangeParamIndex;
        if (index < moduleParams.size()) {
          name = moduleParams[index];
          overridenParams.insert(name);
        } else {
          if (parentFile->Type(expr) != VObjectType::paDelay2) {
            Location loc(parentFile->getFileId(paramAssign),
                         parentFile->Line(paramAssign),
                         parentFile->Column(paramAssign),
                         st->registerSymbol(std::to_string(index)));
            Error err(ErrorDefinition::ELAB_OUT_OF_RANGE_PARAM_INDEX, loc);
            errors->addError(err);
          }
        }

        if (complexV) {
          if (complexV->UhdmType() == UHDM::uhdmconstant) {
            UHDM::constant* c = (UHDM::constant*)complexV;
            const std::string_view v = c->VpiValue();
            value = m_exprBuilder.fromVpiValue(v, c->VpiSize());
          } else if (complexV->UhdmType() == UHDM::uhdmoperation) {
            if (instance) {
              complex = true;
              instance->setComplexValue(name, complexV);
              instance->setOverridenParam(name);
              m_helper.reorderAssignmentPattern(module, p->getUhdmParam(),
                                                complexV, m_compileDesign,
                                                instance, 0);
            }
          }
        }
        if (complex == false) {
          if (value == nullptr)
            value = m_exprBuilder.evalExpr(parentFile, expr, parentInstance,
                                           isTypeParam);
        }

        if ((complex == false) && value && value->isValid()) {
          instance->setValue(name, value, m_exprBuilder,
                             parentFile->Line(expr));
          instance->setOverridenParam(name);
        }

        index++;
      }
    }
  }

  // Command line override
  if (instance->getParent() == nullptr) {  // Top level only
    CommandLineParser* cmdLine =
        m_compileDesign->getCompiler()->getCommandLineParser();
    const auto& useroverrides = cmdLine->getParamList();
    for (const auto& [nameId, value] : useroverrides) {
      const std::string_view name =
          cmdLine->getSymbolTable()->getSymbol(nameId);
      Value* val = m_exprBuilder.fromString(value);
      if (val) {
        instance->setValue(name, val, m_exprBuilder, 0);
        overridenParams.emplace(name);
      }
      Parameter* p = module->getParameter(name);
      if (p) {
        p->setTypespec(nullptr);
        if (UHDM::parameter* param =
                any_cast<UHDM::parameter*>(p->getUhdmParam())) {
          param->Typespec(nullptr);
        }
      }
    }
  }

  // Defparams
  VObjectTypeUnorderedSet types = {VObjectType::paDefparam_assignment};
  VObjectTypeUnorderedSet stopPoints = {
      VObjectType::paConditional_generate_construct,
      VObjectType::paGenerate_module_conditional_statement,
      VObjectType::paGenerate_interface_conditional_statement,
      VObjectType::paLoop_generate_construct,
      VObjectType::paGenerate_module_loop_statement,
      VObjectType::paGenerate_interface_loop_statement,
      VObjectType::paPar_block,
      VObjectType::paSeq_block,
      VObjectType::paModule_declaration};

  std::vector<NodeId> defParams = fC->sl_collect_all(nodeId, types, stopPoints);
  for (auto defParam : defParams) {
    NodeId hIdent = fC->Child(defParam);
    NodeId var;
    fC->Child(hIdent);
    if (fC->Type(hIdent) == VObjectType::paHierarchical_identifier)
      var = fC->Child(hIdent);
    else
      var = hIdent;
    NodeId value = fC->Sibling(hIdent);
    std::string fullPath;
    std::string path;
    while (var) {
      if (fC->Type(var) == VObjectType::slStringConst) {
        fullPath += fC->SymName(var);
      } else if (fC->Type(var) == VObjectType::paConstant_expression) {
        NodeId Constant_primary = fC->Child(var);
        NodeId Primary_literal = fC->Child(Constant_primary);
        NodeId IntConst = fC->Child(Primary_literal);
        const std::string_view name = fC->SymName(IntConst);
        fullPath.append("[").append(name).append("]");
      }
      var = fC->Sibling(var);
      bool isString = false;
      if (fC->Type(var) == VObjectType::slStringConst) {
        isString = true;
      }
      if (var && isString) {
        fullPath += ".";
      }
    }
    for (char c : fullPath) {
      if (c == '.') break;
      path += c;
    }
    std::string pathRoot = StrCat(fC->getLibrary()->getName(), "@", path);
    path = fullPath;

    // path refers to a sub instance
    std::string prefix;
    if (design->findInstance(pathRoot)) {
      std::string p = design->findInstance(pathRoot)->getFullPathName();
      if (p.find('.') != std::string::npos) {
        prefix.assign(instance->getFullPathName()).append(".");
      } else {
        prefix.assign(fC->getLibrary()->getName()).append("@");
      }
    } else {
      prefix = instance->getFullPathName() + ".";
    }
    path = StrCat(prefix, path);
    Value* val = m_exprBuilder.evalExpr(fC, value, instance);
    design->addDefParam(path, fC, hIdent, val);
  }

  if (module) {
    for (FileCNodeId param :
         module->getObjects(VObjectType::paParam_assignment)) {
      NodeId ident = param.fC->Child(param.nodeId);
      const std::string_view name = param.fC->SymName(ident);
      if (overridenParams.find(name) == overridenParams.end()) {
        NodeId exprId = param.fC->Sibling(ident);
        while (param.fC->Type(exprId) == VObjectType::paUnpacked_dimension) {
          exprId = param.fC->Sibling(exprId);
        }
        NodeId Data_type = param.fC->Child(exprId);
        if (instance->getParent() == nullptr) {
          // Top level
          if (exprId == InvalidNodeId) {
            Location loc(param.fC->getFileId(ident), param.fC->Line(ident),
                         param.fC->Column(ident),
                         m_compileDesign->getCompiler()
                             ->getSymbolTable()
                             ->registerSymbol(name));
            Error err(ErrorDefinition::ELAB_TOP_PARAMETER_NO_DEFAULT, loc);
            m_compileDesign->getCompiler()->getErrorContainer()->addError(err);
          }
        }
        if (param.fC->Type(Data_type) != VObjectType::paData_type) {
          // Regular params
          Parameter* p = module->getParameter(name);
          bool isMultidimension = false;
          if (p) {
            isMultidimension = p->isMultidimension();
          }
          if (exprId) {
            m_helper.checkForLoops(true);
            UHDM::expr* expr = (UHDM::expr*)m_helper.compileExpression(
                instance->getDefinition(), param.fC, exprId, m_compileDesign,
                isMultidimension ? Reduce::No : Reduce::Yes, nullptr, instance,
                false);
            m_helper.checkForLoops(false);
            Value* value = nullptr;
            bool complex = false;
            UHDM::typespec* ts = nullptr;
            if (p) {
              ts = p->getTypespec();
              if (UHDM::any* param = p->getUhdmParam()) {
                if (param->UhdmType() == UHDM::uhdmparameter) {
                  if (UHDM::ref_typespec* rt =
                          ((UHDM::parameter*)param)->Typespec()) {
                    ts = rt->Actual_typespec();
                  }
                } else {
                  if (UHDM::ref_typespec* rt =
                          ((UHDM::type_parameter*)param)->Typespec()) {
                    ts = rt->Actual_typespec();
                  }
                }
              }
            }
            if (expr) {
              if (expr->UhdmType() == UHDM::uhdmconstant) {
                UHDM::constant* c = (UHDM::constant*)expr;
                if (ts) {
                  if (ts->UhdmType() != UHDM::uhdmunsupported_typespec) {
                    m_helper.adjustSize(ts, instance->getDefinition(),
                                        m_compileDesign, instance, c);
                    if (c->Typespec() == nullptr) {
                      UHDM::Serializer& s = m_compileDesign->getSerializer();
                      UHDM::ref_typespec* tsRef = s.MakeRef_typespec();
                      tsRef->VpiParent(c);
                      tsRef->Actual_typespec(ts);
                      c->Typespec(tsRef);
                    }
                  }
                }

                const std::string_view v = c->VpiValue();
                value = m_exprBuilder.fromVpiValue(v, c->VpiSize());
                const UHDM::typespec* cts = nullptr;
                if (const UHDM::ref_typespec* rt = c->Typespec()) {
                  cts = rt->Actual_typespec();
                }
                value->setTypespec(cts ? cts : ts);
                if (ts)
                  m_helper.valueRange(value, ts, cts ? cts : ts,
                                      instance->getDefinition(),
                                      m_compileDesign, instance);
              } else if (expr->UhdmType() == UHDM::uhdmoperation) {
                if (instance) {
                  complex = true;
                  expr = (UHDM::expr*)m_helper.defaultPatternAssignment(
                      ts, expr, instance->getDefinition(), m_compileDesign,
                      instance);
                  instance->setComplexValue(name, expr);
                  UHDM::operation* op = (UHDM::operation*)expr;
                  int32_t opType = op->VpiOpType();
                  if (opType == vpiAssignmentPatternOp) {
                    if (ts) {
                      if (m_helper.substituteAssignedValue(expr,
                                                           m_compileDesign)) {
                        expr = m_helper.expandPatternAssignment(
                            ts, expr, module, m_compileDesign, instance);
                      }
                      if (expr) instance->setComplexValue(name, expr);
                    }
                  }
                  if (p) {
                    if (UHDM::typespec* ts = p->getTypespec()) {
                      if (UHDM::any* param = p->getUhdmParam()) {
                        if (param->UhdmType() == UHDM::uhdmparameter) {
                          if (UHDM::ref_typespec* rt =
                                  ((UHDM::parameter*)param)->Typespec()) {
                            ts = rt->Actual_typespec();
                          }
                        } else {
                          if (UHDM::ref_typespec* rt =
                                  ((UHDM::type_parameter*)param)->Typespec()) {
                            ts = rt->Actual_typespec();
                          }
                        }
                      }
                      if (ts->UhdmType() != UHDM::uhdmunsupported_typespec) {
                        if (op->Typespec() == nullptr) {
                          UHDM::Serializer& s =
                              m_compileDesign->getSerializer();
                          UHDM::ref_typespec* tsRef = s.MakeRef_typespec();
                          tsRef->VpiParent(op);
                          op->Typespec(tsRef);
                        }
                        op->Typespec()->Actual_typespec(ts);
                      }
                    }
                    m_helper.reorderAssignmentPattern(module, p->getUhdmParam(),
                                                      expr, m_compileDesign,
                                                      instance, 0);
                  }
                }
              }
            }

            if ((!complex) && (value == nullptr)) {
              value = m_exprBuilder.evalExpr(param.fC, exprId, instance, true);
            }
            if ((!complex) && value && value->isValid()) {
              instance->setValue(name, value, m_exprBuilder, fC->Line(ident));
            }
          }
        }
      }
    }
  }
  return params;
}

void DesignElaboration::checkElaboration_() {
  Design* design = m_compileDesign->getCompiler()->getDesign();
  design->checkDefParamUsage();
  checkConfigurations_();

  // Command line override
  CommandLineParser* cmdLine =
      m_compileDesign->getCompiler()->getCommandLineParser();
  const auto& useroverrides = cmdLine->getParamList();
  for (const auto& [nameId, value] : useroverrides) {
    bool found = false;
    const std::string_view name = cmdLine->getSymbolTable()->getSymbol(nameId);
    for (ModuleInstance* inst : design->getTopLevelModuleInstances()) {
      DesignComponent* module = inst->getDefinition();
      Parameter* p = module->getParameter(name);
      if (p != nullptr) {
        found = true;
        break;
      }
    }
    if (!found) {
      Location loc(
          m_compileDesign->getCompiler()->getSymbolTable()->registerSymbol(
              name));
      Error err(ErrorDefinition::ELAB_UNKNOWN_PARAMETER_COMMAND, loc);
      m_compileDesign->getCompiler()->getErrorContainer()->addError(err);
    }
  }
}

void DesignElaboration::checkConfigurations_() {
  SymbolTable* st = m_compileDesign->getCompiler()->getSymbolTable();
  for (auto& pathUseC : m_cellUseClause) {
    UseClause& useC = pathUseC.second;
    if (!useC.isUsed()) {
      const FileContent* fC = useC.getFileContent();
      Location loc(fC->getFileId(useC.getNodeId()), fC->Line(useC.getNodeId()),
                   fC->Column(useC.getNodeId()),
                   st->registerSymbol(pathUseC.first));
      Error err(ErrorDefinition::ELAB_USE_CLAUSE_IGNORED, loc);
      m_compileDesign->getCompiler()->getErrorContainer()->addError(err);
    }
  }
  for (auto& pathUseC : m_instUseClause) {
    UseClause& useC = pathUseC.second;
    if (!useC.isUsed()) {
      const FileContent* fC = useC.getFileContent();
      Location loc(fC->getFileId(useC.getNodeId()), fC->Line(useC.getNodeId()),
                   fC->Column(useC.getNodeId()),
                   st->registerSymbol(pathUseC.first));
      Error err(ErrorDefinition::ELAB_USE_CLAUSE_IGNORED, loc);
      m_compileDesign->getCompiler()->getErrorContainer()->addError(err);
    }
  }
}

void DesignElaboration::reduceUnnamedBlocks_() {
  Design* design = m_compileDesign->getCompiler()->getDesign();
  UHDM::Serializer& s = m_compileDesign->getSerializer();
  std::queue<ModuleInstance*> queue;
  for (auto instance : design->getTopLevelModuleInstances()) {
    queue.push(instance);
  }

  while (!queue.empty()) {
    ModuleInstance* current = queue.front();
    queue.pop();
    if (current == nullptr) continue;
    for (uint32_t i = 0; i < current->getNbChildren(); i++) {
      queue.push(current->getChildren(i));
    }
    const FileContent* fC = current->getFileContent();
    NodeId id = current->getNodeId();
    VObjectType type = fC->Type(id);

    ModuleInstance* parent = current->getParent();
    if (parent) {
      const FileContent* fCP = parent->getFileContent();
      NodeId idP = parent->getNodeId();
      VObjectType typeP = fCP->Type(idP);

      if ((type == VObjectType::paConditional_generate_construct ||
           type == VObjectType::paGenerate_module_conditional_statement ||
           type == VObjectType::paLoop_generate_construct ||
           type == VObjectType::paGenerate_module_loop_statement ||
           type == VObjectType::paGenerate_interface_loop_statement ||
           type == VObjectType::paGenerate_begin_end_block ||
           type == VObjectType::paGenerate_item) &&
          (typeP == VObjectType::paConditional_generate_construct ||
           typeP == VObjectType::paGenerate_module_conditional_statement ||
           typeP == VObjectType::paGenerate_interface_conditional_statement ||
           typeP == VObjectType::paLoop_generate_construct ||
           typeP == VObjectType::paGenerate_module_loop_statement ||
           typeP == VObjectType::paGenerate_interface_loop_statement ||
           typeP == VObjectType::paGenerate_begin_end_block ||
           typeP == VObjectType::paGenerate_region ||
           typeP == VObjectType::paGenerate_item)) {
        std::string_view fullModName =
            StringUtils::leaf(current->getModuleName());
        std::string_view fullModNameP =
            StringUtils::leaf(parent->getModuleName());
        if (typeP == VObjectType::paGenerate_region) {
          parent->getParent()->overrideParentChild(parent->getParent(), parent,
                                                   current, s);
        } else if (fullModName.find("genblk") != std::string::npos) {
          if (fullModName == fullModNameP) {
            if (fullModNameP.find('[') == std::string::npos) {
              parent->getParent()->overrideParentChild(parent->getParent(),
                                                       parent, current, s);
            }
          }
        } else {
          if (type == VObjectType::paGenerate_item &&
              typeP == VObjectType::paGenerate_item) {
          } else {
            if (fullModNameP.find("genblk") != std::string::npos) {
              if (fullModNameP.find('[') == std::string::npos) {
                parent->getParent()->overrideParentChild(parent->getParent(),
                                                         parent, current, s);
              }
            }
          }
        }
      }
    }
  }
}

void DesignElaboration::bind_ports_nets_(std::vector<Signal*>& ports,
                                         std::vector<Signal*>& signals,
                                         const FileContent* fC,
                                         ModuleInstance* instance,
                                         DesignComponent* mod) {
  for (Signal* port : ports) {
    bindPortType_(port, fC, port->getNodeId(), nullptr, instance, mod,
                  ErrorDefinition::COMP_UNDEFINED_TYPE);
  }
  for (Signal* signal : signals) {
    bindPortType_(signal, signal->getFileContent(), signal->getNodeId(),
                  nullptr, instance, mod, ErrorDefinition::COMP_UNDEFINED_TYPE);
  }
}

bool DesignElaboration::bindDataTypes_(ModuleInstance* instance,
                                       DesignComponent* component) {
  if (component == nullptr) return true;
  if (component->getFileContents().empty()) return true;
  const FileContent* fC = component->getFileContents()[0];
  std::vector<Signal*>& ports = component->getPorts();  // Always empty
  std::vector<Signal*>& signals =
      component->getSignals();  // Variables actually
  bind_ports_nets_(ports, signals, fC, instance, component);
  return true;
}

bool DesignElaboration::bindPackagesDataTypes_() {
  Design* design = m_compileDesign->getCompiler()->getDesign();
  auto packages = design->getPackageDefinitions();
  for (const auto& packNamePair : packages) {
    Package* package = packNamePair.second;
    const FileContent* fC = package->getFileContents()[0];
    std::vector<Signal*>& ports = package->getPorts();  // Always empty
    std::vector<Signal*>& signals =
        package->getSignals();  // Variables actually
    bind_ports_nets_(ports, signals, fC, nullptr, package);
  }
  return true;
}

bool DesignElaboration::bindDataTypes_() {
  Design* design = m_compileDesign->getCompiler()->getDesign();
  auto packages = design->getPackageDefinitions();
  for (const auto& packNamePair : packages) {
    Package* package = packNamePair.second;
    const FileContent* fC = package->getFileContents()[0];
    std::vector<Signal*>& ports = package->getPorts();  // Always empty
    std::vector<Signal*>& signals =
        package->getSignals();  // Variables actually
    bind_ports_nets_(ports, signals, fC, nullptr, package);
  }

  auto modules = design->getModuleDefinitions();
  for (const auto& modNamePair : modules) {
    ModuleDefinition* mod = modNamePair.second;
    VObjectType compType = mod->getType();
    if (mod->getFileContents().empty()) {
      // Built-in primitive
    } else if (compType == VObjectType::paModule_declaration ||
               compType == VObjectType::paInterface_declaration ||
               compType == VObjectType::paConditional_generate_construct ||
               compType == VObjectType::paLoop_generate_construct ||
               compType == VObjectType::paGenerate_item ||
               compType == VObjectType::paGenerate_region ||
               compType ==
                   VObjectType::paGenerate_module_conditional_statement ||
               compType ==
                   VObjectType::paGenerate_interface_conditional_statement ||
               compType == VObjectType::paGenerate_module_loop_statement ||
               compType == VObjectType::paGenerate_interface_loop_statement ||
               compType == VObjectType::paGenerate_module_named_block ||
               compType == VObjectType::paGenerate_interface_named_block ||
               compType == VObjectType::paGenerate_module_block ||
               compType == VObjectType::paGenerate_interface_block ||
               compType == VObjectType::paGenerate_module_item ||
               compType == VObjectType::paGenerate_interface_item ||
               compType == VObjectType::paGenerate_begin_end_block) {
      const FileContent* fC = mod->getFileContents()[0];
      std::vector<Signal*>& ports = mod->getPorts();
      std::vector<Signal*>& signals = mod->getSignals();
      bind_ports_nets_(ports, signals, fC, nullptr, mod);
    }
  }
  auto programs = design->getProgramDefinitions();
  for (const auto& programPair : programs) {
    Program* prog = programPair.second;
    const FileContent* fC = prog->getFileContents()[0];
    std::vector<Signal*>& ports = prog->getPorts();
    std::vector<Signal*>& signals = prog->getSignals();
    bind_ports_nets_(ports, signals, fC, nullptr, prog);
  }
  return true;
}

void DesignElaboration::createFileList_() {
  CommandLineParser* cmdLine =
      m_compileDesign->getCompiler()->getCommandLineParser();
  if (!(cmdLine->writePpOutput() || cmdLine->writePpOutputFileId())) {
    return;
  }

  FileSystem* const fileSystem = FileSystem::getInstance();

  Design* design = m_compileDesign->getCompiler()->getDesign();
  std::queue<ModuleInstance*> queue;
  PathIdSet filePathIds;
  for (const auto& pack : design->getPackageDefinitions()) {
    if (!pack.second->getFileContents().empty()) {
      if (pack.second->getFileContents()[0] != nullptr)
        filePathIds.emplace(pack.second->getFileContents()[0]->getFileId());
    }
  }

  for (auto instance : design->getTopLevelModuleInstances()) {
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
      filePathIds.emplace(fC->getFileId());
    }
    if (def) {
      for (auto f : def->getFileContents()) {
        if (f) {
          filePathIds.emplace(f->getFileId());
        }
      }
    }
  }

  PathId fileId = fileSystem->getChild(
      cmdLine->getCompileDirId(), "file_elab.lst", cmdLine->getSymbolTable());
  std::ostream& ofs = fileSystem->openForWrite(fileId);
  if (ofs.good()) {
    const Compiler::PPFileMap& ppFileName =
        m_compileDesign->getCompiler()->getPPFileMap();
    for (const auto& fileId : filePathIds) {
      auto itr = ppFileName.find(fileId);
      if (itr != ppFileName.end()) {
        for (const auto& fId : itr->second) {
          ofs << fileSystem->toPath(fId) << std::flush << std::endl;
        }
      }
    }
    fileSystem->close(ofs);
  } else {
    std::cerr << "Could not create filelist: " << PathIdPP(fileId) << std::endl;
  }
}
}  // namespace SURELOG
