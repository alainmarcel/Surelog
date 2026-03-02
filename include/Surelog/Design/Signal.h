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
 * File:   Signal.h
 * Author: alain
 *
 * Created on May 6, 2018, 5:32 PM
 */

#ifndef SURELOG_SIGNAL_H
#define SURELOG_SIGNAL_H
#pragma once

#include <Surelog/Common/NodeId.h>
#include <Surelog/SourceCompile/VObjectTypes.h>
#include <uhdm/attribute.h>

#include <string>
#include <string_view>
#include <vector>

namespace SURELOG {

class DataType;
class FileContent;
class ModPort;
class ModuleDefinition;

class Signal final {
 public:
  Signal(const FileContent* fileContent, NodeId node, VObjectType type,
         VObjectType direction, NodeId packedDimension, bool is_signed);
  Signal(const FileContent* fileContent, NodeId node, VObjectType type,
         NodeId packedDimension, VObjectType direction,
         NodeId unpackedDimension, bool is_signed);
  Signal(const FileContent* fileContent, NodeId node, VObjectType type,
         NodeId packedDimension, VObjectType direction, NodeId typeSpecId,
         NodeId unpackedDimension, bool is_signed);
  Signal(const FileContent* fileContent, NodeId node, NodeId interfaceTypeName,
         VObjectType subnettype, NodeId unpackedDimension, bool is_signed);
  Signal(const FileContent* fileContent, NodeId node, NodeId portExpression);

  VObjectType getType() const { return m_type; }
  VObjectType getDirection() const { return m_direction; }
  const FileContent* getFileContent() const { return m_fileContent; }
  NodeId getNodeId() const { return m_nodeId; }
  std::string_view getName() const;
  std::string getInterfaceTypeName() const;

  ModuleDefinition* getInterfaceDef() { return m_interfaceDef; }
  void setInterfaceDef(ModuleDefinition* interfaceDef) {
    m_interfaceDef = interfaceDef;
  }
  ModPort* getModPort() { return m_modPort; }
  void setModPort(ModPort* modport) { m_modPort = modport; }
  void setDirection(VObjectType direction) { m_direction = direction; }
  void setType(VObjectType type) { m_type = type; }
  // For typed net declarations (e.g. "wand integer"), stores the original net
  // keyword (paNetType_Wand/Wor/Wire) separate from the data type in m_type.
  VObjectType getSubNetType() const { return m_subNetType; }
  void setSubNetType(VObjectType t) { m_subNetType = t; }
  void setDataType(const DataType* dtype) { m_dataType = dtype; }
  void setPackedDimension(NodeId id) { m_packedDimension = id; }
  void setUnpackedDimension(NodeId id) { m_unpackedDimension = id; }
  void setTypespecId(NodeId id) { m_typeSpecId = id; }
  bool isInterface() const { return (bool)m_interfaceTypeNameId; }
  void setLowConn(Signal* sig) { m_lowConn = sig; }
  void setConst() { m_const = true; }
  void setVar() { m_var = true; }
  void setLocal() { m_local = true; }
  void setStatic() { m_static = true; }
  void setProtected() { m_protected = true; }
  void setRand() { m_rand = true; }
  void setRandc() { m_randc = true; }
  void setSigned() { m_signed = true; }
  void setExplicitlyNamed() { m_explicitlyNamed = true; }
  bool isConst() const { return m_const; }
  bool isVar() const { return m_var; }
  bool isSigned() const { return m_signed; }
  bool isLocal() const { return m_local; }
  bool isStatic() const { return m_static; }
  bool isProtected() const { return m_protected; }
  bool isRand() const { return m_rand; }
  bool isRandc() const { return m_randc; }
  bool isExplicitlyNamed() const { return m_explicitlyNamed; }
  void setDelay(NodeId id) { m_delay = id; }
  void setDriveStrength(NodeId id) { m_drive_strength = id; }
  void setDefaultValue(NodeId id) { m_default_value = id; }

  Signal* getLowConn() const { return m_lowConn; }
  NodeId getPackedDimension() const { return m_packedDimension; }
  NodeId getUnpackedDimension() const { return m_unpackedDimension; }
  NodeId getModPortId() const;
  NodeId getInterfaceTypeNameId() const { return m_interfaceTypeNameId; }
  NodeId getTypeSpecId() const { return m_typeSpecId; }
  NodeId getDelay() const { return m_delay; }
  NodeId getDriveStrength() const { return m_drive_strength; }
  NodeId getDefaultValue() const { return m_default_value; }
  NodeId getPortExpression() const { return m_port_expression; }
  const DataType* getDataType() const { return m_dataType; }

  std::vector<UHDM::attribute*>* attributes() { return m_attributes; }
  void attributes(std::vector<UHDM::attribute*>* attr) { m_attributes = attr; }

 private:
  const FileContent* m_fileContent = nullptr;
  NodeId m_nodeId;
  VObjectType m_type = VObjectType::slNoType;
  // Preserved original net keyword for typed net declarations (e.g., "wand integer").
  // When set, m_type holds the data type (e.g., paIntegerAtomType_Integer) and
  // m_subNetType holds the net keyword (e.g., paNetType_Wand).
  VObjectType m_subNetType = VObjectType::slNoType;
  VObjectType m_direction = VObjectType::slNoType;
  ModuleDefinition* m_interfaceDef = nullptr;
  ModPort* m_modPort = nullptr;
  const DataType* m_dataType = nullptr;
  Signal* m_lowConn = nullptr;  // for ports
  NodeId m_interfaceTypeNameId;
  NodeId m_packedDimension;
  NodeId m_typeSpecId;
  NodeId m_unpackedDimension;
  NodeId m_delay;
  NodeId m_drive_strength;
  NodeId m_default_value;
  NodeId m_port_expression;
  bool m_const = false;
  bool m_var = false;
  bool m_signed = false;
  bool m_local = false;
  bool m_static = false;
  bool m_protected = false;
  bool m_rand = false;
  bool m_randc = false;
  bool m_explicitlyNamed = false;
  std::vector<UHDM::attribute*>* m_attributes = nullptr;
};

}  // namespace SURELOG

#endif /* SURELOG_SIGNAL_H */
