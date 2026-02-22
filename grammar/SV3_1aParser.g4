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

parser grammar SV3_1aParser;

options {
  tokenVocab = SV3_1aLexer;
}

@parser::members {

  void getCallingContext(antlr4::ParserRuleContext* ctx, std::vector<size_t>& context) {
    antlr4::ParserRuleContext* current = ctx;
    while (current != nullptr) {
      context.push_back(current->getRuleIndex());
      current = dynamic_cast<antlr4::ParserRuleContext*>(current->parent);
    }
  }

  bool isInterfaceGenerator(antlr4::ParserRuleContext* ctx) {
    std::vector<size_t> parent_ids(20);
    getCallingContext(ctx, parent_ids);

    bool isModuleOrProgramBlock = false;
    for (size_t rule_type : parent_ids) {
      if (!isModuleOrProgramBlock) {
        if (rule_type == RuleChecker_declaration) {
          return false;
        }

        switch (rule_type) {
          case RuleModule_declaration:
          case RuleProgram_declaration: isModuleOrProgramBlock = true;
        }

        // First thing we found was an interface declration
        if (rule_type == RuleInterface_declaration) {
          return true;
        }
      }

      // At this point we're either a program or a module, and trying to make
      // sure that we don't have an interface in our ancestor chain. Spec says
      // if we do we must return true
      if (rule_type == RuleInterface_declaration) {
        return true;
      }
    }

    return false;
  }

  bool isCheckerGenerator(antlr4::ParserRuleContext* ctx) {
    std::vector<size_t> parent_ids(20);
    getCallingContext(ctx, parent_ids);

    // In the SV Spec it states that a Checker Generator is only valid if the
    // generate block is both checker.
    for (size_t rule_type : parent_ids) {
      switch (rule_type) {
        case RuleModule_declaration:
        case RuleInterface_declaration:
        case RuleProgram_declaration: return false;
      }

      if (rule_type == RuleChecker_declaration) {
        return true;
      }
    }

    return false;
  }

  bool isModuleGenerator(antlr4::ParserRuleContext* ctx) {
    std::vector<size_t> parent_ids(20);
    getCallingContext(ctx, parent_ids);

    bool isGenerateInAModuleDeclaration = false;

    // In the SV Spec it states that a Module Generator is only valid if the
    // generate block is both within a module, and that module is not a child
    // of an interface block. This code will first make sure the generate
    // block is in a module, and then verify it is not a child of an interface
    // block.
    for (size_t rule_type : parent_ids) {
      if (!isGenerateInAModuleDeclaration) {
        switch (rule_type) {
          case RuleChecker_declaration:
          case RuleInterface_declaration: return false;
        }

        // Treat programs as modules
        if (rule_type == RuleModule_declaration || rule_type == RuleProgram_declaration) {
          isGenerateInAModuleDeclaration = true;
        }
      }
      // We are in a module, and only return false if we find an interface
      // declaration in our ancestors.

      if (rule_type == RuleInterface_declaration) {
        return false;
      }
    }

    return true;
  }
}

top_level_rule: null_rule source_text EOF; // SV files

top_level_library_rule: null_rule library_text EOF; // .map files

library_text: library_descriptions*;

library_descriptions
  : library_declaration
  | include_statement
  | config_declaration
  | SEMICOLON
  ;

library_declaration
  : LIBRARY identifier file_path_spec (COMMA file_path_spec)* (
    INCDIR file_path_spec (COMMA file_path_spec)*
  )? SEMICOLON
  ;

file_path_spec
  : (Simple_identifier | DIV | DOT | STAR | DOTSTAR | QMARK)+
  ;

include_statement: INCLUDE file_path_spec SEMICOLON;

source_text: timeunits_declaration? description*;

null_rule
  :
  ; // Placeholder rule that create the "0" VObject, DO NOT REMOVE

description
  : module_declaration
  | udp_declaration
  | interface_declaration
  | program_declaration
  | package_declaration
  | surelog_macro_not_defined
  | attribute_instance* (package_item | bind_directive)
  | config_declaration
  | top_directives
  ;

module_nonansi_header
  : attribute_instance* module_keyword lifetime? identifier package_import_declaration*
      parameter_port_list? list_of_ports SEMICOLON
  ;

module_ansi_header
  : attribute_instance* module_keyword lifetime? identifier package_import_declaration*
      parameter_port_list? list_of_port_declarations? SEMICOLON
  ;

module_declaration
  : module_nonansi_header timeunits_declaration? module_item* ENDMODULE (
    COLON identifier
  )?
  | module_ansi_header timeunits_declaration? non_port_module_item* ENDMODULE (
    COLON identifier
  )?
  | attribute_instance* module_keyword lifetime? identifier OPEN_PARENS DOT STAR CLOSE_PARENS
      SEMICOLON timeunits_declaration? module_item* ENDMODULE (
    COLON identifier
  )?
  | EXTERN module_nonansi_header
  | EXTERN module_ansi_header
  ;

module_keyword: MODULE | MACROMODULE;

interface_nonansi_header
  : attribute_instance* INTERFACE lifetime? interface_identifier package_import_declaration*
      parameter_port_list? list_of_ports SEMICOLON
  ;

interface_ansi_header
  : attribute_instance* INTERFACE lifetime? interface_identifier package_import_declaration*
      parameter_port_list? list_of_port_declarations? SEMICOLON
  ;

interface_declaration
  : interface_nonansi_header timeunits_declaration? interface_item* ENDINTERFACE (
    COLON interface_identifier
  )?
  | interface_ansi_header timeunits_declaration? non_port_interface_item* ENDINTERFACE (
    COLON interface_identifier
  )?
  | attribute_instance? INTERFACE interface_identifier OPEN_PARENS DOT STAR CLOSE_PARENS SEMICOLON
      timeunits_declaration? interface_item* ENDINTERFACE (
    COLON interface_identifier
  )?
  | EXTERN interface_nonansi_header
  | EXTERN interface_ansi_header
  ;

program_nonansi_header
  : (attribute_instance) PROGRAM lifetime? identifier package_import_declaration*
      parameter_port_list? list_of_ports SEMICOLON
  ;

program_ansi_header
  : attribute_instance* PROGRAM lifetime? identifier package_import_declaration* parameter_port_list
      ? list_of_port_declarations? SEMICOLON
  ;

checker_declaration
  : CHECKER identifier (
    OPEN_PARENS checker_port_list? CLOSE_PARENS
  )? SEMICOLON (attribute_instance* checker_or_generate_item)* ENDCHECKER (
    COLON identifier
  )?
  ;

program_declaration
  : program_nonansi_header timeunits_declaration? program_item* ENDPROGRAM (
    COLON identifier
  )?
  | program_ansi_header timeunits_declaration? non_port_program_item* ENDPROGRAM (
    COLON identifier
  )?
  | attribute_instance* PROGRAM identifier OPEN_PARENS DOT STAR CLOSE_PARENS SEMICOLON
      timeunits_declaration? program_item* ENDPROGRAM (
    COLON identifier
  )?
  | EXTERN program_nonansi_header
  | EXTERN program_ansi_header
  ;

class_declaration
  : VIRTUAL? CLASS lifetime? identifier parameter_port_list? (
    EXTENDS class_type (
      OPEN_PARENS list_of_arguments CLOSE_PARENS
    )?
  )? (
    IMPLEMENTS interface_class_type (COMMA interface_class_type)*
  )? SEMICOLON class_item* ENDCLASS (COLON identifier)?
  ;

interface_class_type: ps_identifier parameter_value_assignment?;

interface_class_declaration
  : INTERFACE CLASS identifier parameter_port_list? (
    EXTENDS interface_class_type (COMMA interface_class_type)*
  )? SEMICOLON interface_class_item* ENDCLASS (COLON identifier)?
  ;

interface_class_item
  : type_declaration
  | attribute_instance* interface_class_method SEMICOLON
  | local_parameter_declaration SEMICOLON
  | parameter_declaration SEMICOLON
  | SEMICOLON
  ;

interface_class_method: PURE VIRTUAL method_prototype;

package_declaration
  : attribute_instance* PACKAGE identifier SEMICOLON timeunits_declaration? (
    attribute_instance* package_item
  )* ENDPACKAGE (COLON identifier)?
  ;

timeunits_declaration
  : TIMEUNIT time_literal DIV time_literal SEMICOLON                     # TimeUnitsDecl_TimeUnitDiv
  | TIMEUNIT time_literal SEMICOLON                                      # TimeUnitsDecl_TimeUnit
  | TIMEPRECISION time_literal SEMICOLON                                 # TimeUnitsDecl_TimePrecision
  | TIMEUNIT time_literal SEMICOLON TIMEPRECISION time_literal SEMICOLON #
      TimeUnitsDecl_TimeUnitTimePrecision
  | TIMEPRECISION time_literal SEMICOLON TIMEUNIT time_literal SEMICOLON #
      TimeUnitsDecl_TimePrecisionTimeUnit
  ;

parameter_port_list
  : POUND OPEN_PARENS list_of_param_assignments (
    COMMA parameter_port_declaration
  )* CLOSE_PARENS
  | POUND OPEN_PARENS parameter_port_declaration (
    COMMA parameter_port_declaration
  )* CLOSE_PARENS
  | POUND OPEN_PARENS CLOSE_PARENS
  ;

parameter_port_declaration
  : parameter_declaration
  | local_parameter_declaration
  | data_type list_of_param_assignments
  | TYPE list_of_type_assignments
  ;

list_of_ports: OPEN_PARENS port (COMMA port)* CLOSE_PARENS;

list_of_port_declarations
  : OPEN_PARENS (
    attribute_instance* ansi_port_declaration (
      COMMA attribute_instance* ansi_port_declaration
    )*
  )? CLOSE_PARENS
  ;

port_declaration
  : attribute_instance* (
    inout_declaration
    | input_declaration
    | output_declaration
    | ref_declaration
    | interface_port_declaration
  )
  ;

port
  : port_expression?
  | DOT identifier OPEN_PARENS port_expression? CLOSE_PARENS
  ;

port_expression
  : port_reference
  | OPEN_CURLY port_reference (COMMA port_reference)* CLOSE_CURLY
  ;

port_reference: identifier constant_select;

port_direction: INPUT | OUTPUT | INOUT | REF;

net_port_header: port_direction? net_port_type;

variable_port_header: port_direction? variable_port_type;

interface_port_header
  : interface_identifier (DOT identifier)?
  | INTERFACE (DOT identifier)?
  ;

ansi_port_declaration
  : (net_port_header | interface_port_header) identifier unpacked_dimension* (
    ASSIGN_OP constant_expression
  )?
  | variable_port_header? identifier variable_dimension* (
    ASSIGN_OP constant_expression
  )?
  | (net_port_header | variable_port_header) DOT identifier OPEN_PARENS expression? CLOSE_PARENS
  ;

elaboration_system_task
  : DOLLAR Simple_identifier (
    (OPEN_PARENS number (COMMA list_of_arguments)? CLOSE_PARENS)? SEMICOLON
    | (OPEN_PARENS list_of_arguments CLOSE_PARENS)? SEMICOLON
  )
  ;

module_common_item
  : module_or_generate_item_declaration
  | module_instantiation
  | assertion_item
  | bind_directive
  | continuous_assign
  | net_alias
  | initial_construct
  | final_construct
  | always_construct
  | loop_generate_construct
  | conditional_generate_construct
  | elaboration_system_task
  | system_task
  ;

module_item: port_declaration SEMICOLON | non_port_module_item;

module_or_generate_item
  : attribute_instance* (
    parameter_override
    | gate_instantiation
    | udp_instantiation
    | module_instantiation
    | module_common_item
  )
  ;

module_or_generate_item_declaration
  : package_or_generate_item_declaration
  | genvar_declaration
  | clocking_declaration
  | DEFAULT CLOCKING identifier SEMICOLON
  | DEFAULT DISABLE IFF expression_or_dist SEMICOLON
  ;

non_port_module_item
  : generate_region
  | module_or_generate_item
  | specify_block
  | attribute_instance* specparam_declaration
  | program_declaration
  | module_declaration
  | timeunits_declaration
  | system_task SEMICOLON
  | surelog_macro_not_defined
  | pragma_directive
  ;

parameter_override
  : DEFPARAM list_of_defparam_assignments SEMICOLON
  ;

bind_directive
  : BIND identifier (
    COLON? identifier constant_bit_select (
      COMMA identifier constant_bit_select
    )*
  )? bind_instantiation
  ;

bind_instantiation
  : module_instantiation
  | checker_instantiation
  ;

interface_or_generate_item
  : attribute_instance* (
    module_common_item
    | MODPORT modport_item (COMMA modport_item)* SEMICOLON
    | extern_tf_declaration
  )
  ;

extern_tf_declaration
  : EXTERN method_prototype SEMICOLON
  | EXTERN FORKJOIN task_prototype SEMICOLON
  ;

interface_item
  : port_declaration SEMICOLON
  | non_port_interface_item
  ;

non_port_interface_item
  : generated_interface_instantiation
  | attribute_instance* specparam_declaration
  | interface_or_generate_item
  | program_declaration
  | interface_declaration
  | timeunits_declaration
  | surelog_macro_not_defined
  ;

program_item
  : port_declaration SEMICOLON
  | non_port_program_item
  ;

non_port_program_item
  : attribute_instance* (
    continuous_assign
    | module_or_generate_item_declaration
    | specparam_declaration
    | initial_construct
    | final_construct
    | concurrent_assertion_item
  )
  | timeunits_declaration
  | program_generate_item
  | surelog_macro_not_defined
  ;

program_generate_item
  : loop_generate_construct
  | conditional_generate_construct
  | generate_region
  | elaboration_system_task
  ;

checker_port_list: checker_port_item (COMMA checker_port_item)*;

checker_port_item
  : attribute_instance* (INPUT | OUTPUT)? property_formal_type identifier variable_dimension* (
    ASSIGN_OP property_actual_arg
  )?
  ;

checker_or_generate_item
  : checker_or_generate_item_declaration
  | initial_construct
  | always_construct
  | final_construct
  | assertion_item
  | continuous_assign
  | checker_generate_item
  ;

checker_or_generate_item_declaration
  : RAND* data_declaration
  | function_declaration
  | checker_declaration
  | assertion_item_declaration
  | covergroup_declaration
  | overload_declaration
  | genvar_declaration
  | clocking_declaration
  | DEFAULT CLOCKING identifier SEMICOLON
  | DEFAULT DISABLE IFF expression_or_dist SEMICOLON
  | SEMICOLON
  | surelog_macro_not_defined
  ;

checker_generate_item
  : loop_generate_construct
  | conditional_generate_construct
  | generate_region
  | elaboration_system_task
  ;

class_item
  : attribute_instance* (
    class_property
    | class_method
    | class_constraint
    | type_declaration
    | class_declaration
    | covergroup_declaration
  )
  | local_parameter_declaration SEMICOLON
  | parameter_declaration SEMICOLON
  | surelog_macro_not_defined
  | SEMICOLON
  ;

class_property
  : const_type? property_qualifier* data_declaration
  | const_type class_item_qualifier* data_type identifier (
    ASSIGN_OP constant_expression
  )? SEMICOLON
  ;

pure_virtual_qualifier: PURE VIRTUAL;

extern_qualifier: EXTERN;

class_method
  : method_qualifier* (
    task_declaration
    | function_declaration
    | class_constructor_declaration
  )
  | pure_virtual_qualifier class_item_qualifier* method_prototype SEMICOLON
  | extern_qualifier method_qualifier* (
    method_prototype SEMICOLON
    | class_constructor_prototype
  )
  ;

class_constructor_prototype
  : FUNCTION NEW (OPEN_PARENS tf_port_list? CLOSE_PARENS)?
  ;

class_constraint: constraint_prototype | constraint_declaration;

class_item_qualifier
  : STATIC    # ClassItemQualifier_Static
  | PROTECTED # ClassItemQualifier_Protected
  | LOCAL     # ClassItemQualifier_Local
  ;

property_qualifier
  : RAND                 # PropQualifier_Rand
  | RANDC                # PropQualifier_Randc
  | class_item_qualifier # PropQualifier_ClassItem
  ;

method_qualifier
  : VIRTUAL              # MethodQualifier_Virtual
  | class_item_qualifier # MethodQualifier_ClassItem
  ;

method_prototype: task_prototype | function_prototype;

super_dot_new: SUPER DOT NEW;

class_constructor_declaration
  : FUNCTION class_scope? NEW (
    OPEN_PARENS tf_port_list? CLOSE_PARENS
  )? SEMICOLON block_item_declaration* (
    super_dot_new (OPEN_PARENS list_of_arguments CLOSE_PARENS)? SEMICOLON
  )? function_statement_or_null* ENDFUNCTION (COLON NEW)?
  ;

constraint_declaration
  : STATIC? CONSTRAINT identifier constraint_block
  ;

constraint_block: OPEN_CURLY constraint_block_item* CLOSE_CURLY;

constraint_block_item
  : SOLVE solve_before_list BEFORE solve_before_list SEMICOLON
  | constraint_expression
  ;

solve_before_list
  : constraint_primary (COMMA constraint_primary)*
  ;

constraint_primary
  : (implicit_class_handle DOT | class_scope)? dollar_root_keyword? identifier (
    (OPEN_BRACKET constant_expression CLOSE_BRACKET)* DOT identifier
  )* select
  ;

constraint_expression
  : SOFT? expression_or_dist SEMICOLON
  | uniqueness_constraint SEMICOLON
  | expression IMPLY constraint_set
  | IF OPEN_PARENS expression CLOSE_PARENS constraint_set (
    ELSE constraint_set
  )?
  | FOREACH OPEN_PARENS ps_or_hierarchical_array_identifier OPEN_BRACKET loop_variables
      CLOSE_BRACKET CLOSE_PARENS constraint_set
  | DISABLE SOFT constraint_primary SEMICOLON
  ;

uniqueness_constraint
  : UNIQUE OPEN_CURLY open_range_list CLOSE_CURLY
  ;

constraint_set
  : constraint_expression
  | OPEN_CURLY constraint_expression* CLOSE_CURLY
  ;

dist_list: dist_item (COMMA dist_item)*;

dist_item: value_range dist_weight?;

/* Replaced by COLON DIV :  ASSIGN_RANGE : ':/' ; */
dist_weight
  : ASSIGN_VALUE expression # DistWeight_AssignValue
  | COLON DIV expression    # DistWeight_AssignRange
  ;

constraint_prototype
  : (extern_qualifier | pure_keyword)? STATIC? CONSTRAINT identifier SEMICOLON
  ;

extern_constraint_declaration
  : STATIC? CONSTRAINT class_scope identifier constraint_block
  ;

identifier_list: identifier (COMMA identifier)*;

package_item
  : package_or_generate_item_declaration
  | specparam_declaration
  | anonymous_program
  | package_export_declaration
  | timeunits_declaration
  ;

package_or_generate_item_declaration
  : net_declaration
  | data_declaration
  | task_declaration
  | function_declaration
  | checker_declaration
  | dpi_import_export
  | extern_constraint_declaration
  | class_declaration
  | interface_class_declaration
  | class_constructor_declaration
  | parameter_declaration SEMICOLON
  | local_parameter_declaration SEMICOLON
  | covergroup_declaration
  | overload_declaration
  | assertion_item_declaration
  | SEMICOLON
  ;

anonymous_program
  : PROGRAM SEMICOLON anonymous_program_item* ENDPROGRAM
  ;

anonymous_program_item
  : task_declaration
  | function_declaration
  | class_declaration
  | covergroup_declaration
  | class_constructor_declaration
  | SEMICOLON
  | surelog_macro_not_defined
  ;

local_parameter_declaration
  : LOCALPARAM (data_type_or_implicit | TYPE) list_of_param_assignments
  ;

parameter_declaration
  : PARAMETER (data_type_or_implicit | TYPE) list_of_param_assignments
  ;

specparam_declaration
  : SPECPARAM packed_dimension? list_of_specparam_assignments SEMICOLON
  ;

inout_declaration: INOUT net_port_type list_of_port_identifiers;

input_declaration
  : INPUT (
    net_port_type list_of_port_identifiers
    | variable_port_type? list_of_variable_identifiers
  )
  ;

output_declaration
  : OUTPUT (
    net_port_type list_of_port_identifiers
    | variable_port_type? list_of_variable_port_identifiers
  )
  ;

interface_port_declaration
  : interface_identifier list_of_interface_identifiers
  | interface_identifier DOT identifier list_of_interface_identifiers
  ;

ref_declaration
  : REF variable_port_type list_of_variable_identifiers
  ;

data_declaration
  : const_type? (
    lifetime? variable_declaration
    | var_type lifetime? variable_impl_declaration
  )
  | type_declaration
  | package_import_declaration
  | net_type_declaration
  ;

variable_impl_declaration
  : (
    data_type_or_implicit
    | signing packed_dimension*
    | packed_dimension+
  ) list_of_variable_decl_assignments SEMICOLON
  ;

variable_declaration
  : (data_type | OPEN_PARENS data_type CLOSE_PARENS | signing packed_dimension* | packed_dimension+) list_of_variable_decl_assignments
      SEMICOLON
  ;

package_import_declaration
  : IMPORT package_import_item (COMMA package_import_item)* SEMICOLON
  ;

package_import_item: identifier COLONCOLON (identifier | STAR);

package_export_declaration
  : EXPORT STARCOLONCOLONSTAR SEMICOLON
  | EXPORT package_import_item (COMMA package_import_item)? SEMICOLON
  ;

genvar_declaration: GENVAR identifier_list SEMICOLON;

net_declaration
  : net_type (drive_strength | charge_strength)? (
    VECTORED
    | SCALARED
  )? data_type_or_implicit delay3? list_of_net_decl_assignments SEMICOLON
  | identifier delay_control? list_of_net_decl_assignments SEMICOLON
  | INTERCONNECT implicit_data_type pound_delay_value? identifier unpacked_dimension* (
    COMMA identifier unpacked_dimension*
  )? SEMICOLON
  ;

type_declaration
  : TYPEDEF (
    ((data_type | net_type) identifier variable_dimension*)
    | (identifier constant_bit_select DOT identifier identifier)
    | (
      (
        enum_keyword
        | struct_keyword
        | union_keyword
        | class_keyword
        | interface_class_keyword
      )? identifier
    )
  ) SEMICOLON
  ;

enum_keyword: ENUM;

struct_keyword: STRUCT;

union_keyword: UNION;

class_keyword: CLASS;

interface_class_keyword: INTERFACE CLASS;

net_type_declaration
  : NETTYPE (
    (
      data_type identifier (
        WITH (package_scope | class_scope)? identifier
      )?
    )
    | ((package_scope | class_scope)? identifier identifier)
  ) SEMICOLON
  ;

lifetime
  : STATIC    # Lifetime_Static
  | AUTOMATIC # Lifetime_Automatic
  ;

casting_type
  : simple_type
  | primary_literal
  | (package_scope | class_scope)? identifier constant_select (
    OPEN_BRACKET constant_range_expression CLOSE_BRACKET
  )?
  // | constant_concatenation (OPEN_BRACKET constant_range_expression CLOSE_BRACKET)? |
  // constant_multiple_concatenation (OPEN_BRACKET constant_range_expression CLOSE_BRACKET)? |
  // subroutine_call | OPEN_PARENS constant_mintypmax_expression CLOSE_PARENS
  | OPEN_PARENS constant_expression CLOSE_PARENS
  // | casting_type TICK (OPEN_PARENS constant_expression CLOSE_PARENS | constant_concatenation |
  // constant_multiple_concatenation) | constant_assignment_pattern_expression | type_reference
  | signing
  | string_type
  | const_type
  | system_task
  ;

data_type
  : integer_vector_type signing? packed_dimension*
  | integer_atom_type signing?
  | non_integer_type
  | struct_union (packed_keyword signing?)? OPEN_CURLY struct_union_member struct_union_member*
      CLOSE_CURLY packed_dimension*
  | ENUM enum_base_type? OPEN_CURLY enum_name_declaration (
    COMMA enum_name_declaration
  )* CLOSE_CURLY
  | string_type
  | chandle_type
  | VIRTUAL INTERFACE? interface_identifier parameter_value_assignment? (
    DOT identifier
  )?
  | (class_scope | package_scope)? identifier (
    packed_dimension+
    | (
      parameter_value_assignment? (
        COLONCOLON identifier parameter_value_assignment?
      )*
    )
  )
  | event_type
  | type_reference
  ;

packed_keyword: PACKED;

string_type: STRING;

string_value: String;

chandle_type: CHANDLE;

event_type: EVENT;

const_type: CONST;

var_type: VAR;

data_type_or_implicit: data_type | signing? packed_dimension*;

implicit_data_type: signing? packed_dimension*;

enum_base_type
  : integer_atom_type signing?
  | integer_vector_type signing? packed_dimension?
  | identifier packed_dimension?
  ;

enum_name_declaration
  : identifier (
    OPEN_BRACKET Integral_number (COLON Integral_number)? CLOSE_BRACKET
  )? (ASSIGN_OP constant_expression)?
  ;

class_scope: class_type COLONCOLON;

// identifier was inlined to lexer tokens for parsing speed
class_type
  : (
    Simple_identifier
    | Escaped_identifier
    | THIS
    | RANDOMIZE
    | SAMPLE
    | DOLLAR_UNIT
  ) parameter_value_assignment? (
    COLONCOLON identifier parameter_value_assignment?
  )*
  ;

integer_type: integer_vector_type | integer_atom_type;

integer_atom_type
  : BYTE
  | SHORTINT
  | INT
  | LONGINT
  | INTEGER
  | TIME
  ;

integer_vector_type: BIT | LOGIC | REG;

non_integer_type: SHORTREAL | REAL | REALTIME;

net_type
  : SUPPLY0
  | SUPPLY1
  | TRI
  | TRIAND
  | TRIOR
  | TRIREG
  | TRI0
  | TRI1
  | UWIRE
  | WIRE
  | WAND
  | WOR
  ;

net_port_type
  : net_type? data_type_or_implicit
  | identifier
  | INTERCONNECT implicit_data_type
  ;

variable_port_type
  : var_data_type
  | OPEN_BRACKET constant_range CLOSE_BRACKET
  ;

var_data_type: data_type | var_type data_type_or_implicit;

signing: SIGNED | UNSIGNED;

simple_type
  : integer_type
  | non_integer_type
  | ps_type_identifier
  ;

random_qualifier
  : RAND  # RandomQualifier_Rand
  | RANDC # RandomQualifier_RandC
  ;

struct_union_member
  : attribute_instance* random_qualifier? data_type_or_void list_of_variable_decl_assignments
      SEMICOLON
  ;

data_type_or_void: data_type | VOID;

struct_union: struct_keyword | union_keyword tagged_keyword?;

tagged_keyword: TAGGED;

type_reference
  : TYPE OPEN_PARENS (expression | data_type) CLOSE_PARENS
  ;

drive_strength
  : OPEN_PARENS (SUPPLY0 | STRONG0 | PULL0 | WEAK0) COMMA (
    SUPPLY1
    | STRONG1
    | PULL1
    | WEAK1
    | HIGHZ1
  ) CLOSE_PARENS
  | OPEN_PARENS (SUPPLY1 | STRONG1 | PULL1 | WEAK1 | HIGHZ1) COMMA (
    SUPPLY0
    | STRONG0
    | PULL0
    | WEAK0
    | HIGHZ0
  ) CLOSE_PARENS
  | OPEN_PARENS HIGHZ0 COMMA (SUPPLY1 | STRONG1 | PULL1 | WEAK1) CLOSE_PARENS
  | OPEN_PARENS HIGHZ1 COMMA (SUPPLY0 | STRONG0 | PULL0 | WEAK0) CLOSE_PARENS
  ;

strength0: SUPPLY0 | STRONG0 | PULL0 | WEAK0;

strength1: SUPPLY1 | STRONG1 | PULL1 | WEAK1;

charge_strength: SMALL | MEDIUM | LARGE;

delay3
  : pound_delay_value
  | POUND OPEN_PARENS mintypmax_expression (
    COMMA mintypmax_expression (COMMA mintypmax_expression)?
  )? CLOSE_PARENS
  ;

delay2
  : pound_delay_value
  | POUND OPEN_PARENS mintypmax_expression (
    COMMA mintypmax_expression
  )? CLOSE_PARENS
  ;

pound_delay_value
  : Pound_Pound_delay time_unit?
  | Pound_delay time_unit?
  | POUND delay_value
  ;

delay_value
  : Integral_number
  | Real_number
  | ps_identifier
  | time_literal
  | ONESTEP
  | ps_or_hierarchical_identifier
  ; //REMOVED  | Decimal_number

list_of_defparam_assignments
  : defparam_assignment (COMMA defparam_assignment)*
  ;

list_of_interface_identifiers
  : interface_identifier unpacked_dimension* (
    COMMA interface_identifier unpacked_dimension*
  )*
  ;

list_of_net_decl_assignments
  : net_decl_assignment (COMMA net_decl_assignment)*
  ;

list_of_param_assignments
  : param_assignment (COMMA param_assignment)*
  ;

list_of_port_identifiers
  : identifier unpacked_dimension* (
    COMMA identifier unpacked_dimension*
  )*
  ;

list_of_specparam_assignments
  : specparam_assignment (COMMA specparam_assignment)*
  ;

list_of_tf_variable_identifiers
  : identifier variable_dimension* (ASSIGN_OP expression)? (
    COMMA identifier variable_dimension* (ASSIGN_OP expression)?
  )*
  ;

list_of_type_assignments
  : (identifier (ASSIGN_OP data_type)?) (
    COMMA (identifier (ASSIGN_OP data_type)?)
  )*
  ;

list_of_variable_decl_assignments
  : variable_decl_assignment (COMMA variable_decl_assignment)*
  ;

list_of_variable_identifiers
  : identifier variable_dimension* (
    COMMA identifier variable_dimension*
  )*
  ;

list_of_variable_port_identifiers
  : identifier variable_dimension* (
    ASSIGN_OP constant_expression
  )? (
    COMMA identifier variable_dimension* (
      ASSIGN_OP constant_expression
    )?
  )*
  ;

list_of_virtual_interface_decl
  : identifier (ASSIGN_OP identifier)? (
    COMMA identifier (ASSIGN_OP identifier)?
  )*
  ;

defparam_assignment
  : (identifier | hierarchical_identifier) ASSIGN_OP constant_mintypmax_expression
  ;

net_decl_assignment
  : identifier unpacked_dimension* (ASSIGN_OP expression)?
  ;

param_assignment
  : identifier unpacked_dimension* (
    ASSIGN_OP constant_param_expression
  )?
  ;

specparam_assignment
  : identifier ASSIGN_OP constant_mintypmax_expression
  | pulse_control_specparam
  ;

pulse_control_specparam
  : PATHPULSE DOLLAR ASSIGN_OP OPEN_PARENS constant_mintypmax_expression (
    COMMA constant_mintypmax_expression
  )? CLOSE_PARENS SEMICOLON
  | PATHPULSE DOLLAR specify_input_terminal_descriptor DOLLAR specify_output_terminal_descriptor
      ASSIGN_OP OPEN_PARENS constant_mintypmax_expression (
    COMMA constant_mintypmax_expression
  )? CLOSE_PARENS SEMICOLON
  ;

variable_decl_assignment
  : identifier (
    (ASSIGN_OP class_new)
    | (
      unsized_dimension variable_dimension* (
        ASSIGN_OP dynamic_array_new
      )?
    )
    | (
      ASSIGN_OP NEW (OPEN_PARENS list_of_arguments CLOSE_PARENS)?
    )
    | (variable_dimension* (ASSIGN_OP expression)?)
  )
  ; //        | ASSIGN_OP NEW (OPEN_PARENS list_of_arguments CLOSE_PARENS)?

class_new
  : class_scope? NEW (
    OPEN_PARENS list_of_arguments CLOSE_PARENS
    | expression
  )?
  ;

dynamic_array_new
  : NEW OPEN_BRACKET expression CLOSE_BRACKET (
    OPEN_PARENS expression CLOSE_PARENS
  )?
  ;

unpacked_dimension
  : OPEN_BRACKET constant_range CLOSE_BRACKET
  | OPEN_BRACKET constant_expression CLOSE_BRACKET
  | unsized_dimension
  ;

packed_dimension
  : OPEN_BRACKET constant_range CLOSE_BRACKET
  | unsized_dimension
  ;

associative_dimension
  : OPEN_BRACKET data_type CLOSE_BRACKET
  | ASSOCIATIVE_UNSPECIFIED
  ;

variable_dimension
  : unsized_dimension
  | unpacked_dimension
  | associative_dimension
  | queue_dimension
  ;

queue_dimension
  : OPEN_BRACKET DOLLAR (COLON constant_expression)? CLOSE_BRACKET
  ;

unsized_dimension: OPEN_BRACKET CLOSE_BRACKET;

function_data_type: data_type | VOID;

function_data_type_or_implicit
  : function_data_type
  | signing? packed_dimension*
  ;

function_declaration
  : FUNCTION lifetime? function_body_declaration
  ;

function_body_declaration
  : function_data_type_or_implicit (
    interface_identifier DOT
    | class_scope
  )? identifier SEMICOLON tf_item_declaration* function_statement_or_null* ENDFUNCTION (
    COLON identifier
  )?
  | function_data_type_or_implicit (
    interface_identifier DOT
    | class_scope
  )? identifier OPEN_PARENS tf_port_list? CLOSE_PARENS SEMICOLON block_item_declaration*
      function_statement_or_null* ENDFUNCTION (COLON identifier)?
  ;

function_prototype
  : FUNCTION function_data_type_or_implicit identifier (
    OPEN_PARENS tf_port_list? CLOSE_PARENS
  )?
  ;

dpi_import_export
  : IMPORT string_value (context_keyword | pure_keyword)? (
    Simple_identifier ASSIGN_OP
  )? function_prototype SEMICOLON
  | IMPORT string_value context_keyword? (
    Simple_identifier ASSIGN_OP
  )? task_prototype SEMICOLON
  | EXPORT string_value (Simple_identifier ASSIGN_OP)? (
    function_name_decl
    | task_name_decl
  ) SEMICOLON
  ;

context_keyword: CONTEXT;

function_name_decl: FUNCTION identifier;

task_name_decl: TASK identifier;

pure_keyword: PURE;

task_declaration: TASK lifetime? task_body_declaration;

task_body_declaration
  : (interface_identifier DOT | class_scope)? identifier SEMICOLON tf_item_declaration*
      statement_or_null* ENDTASK (COLON identifier)?
  | (interface_identifier DOT | class_scope)? identifier OPEN_PARENS tf_port_list? CLOSE_PARENS
      SEMICOLON block_item_declaration* statement_or_null* ENDTASK (
    COLON identifier
  )?
  ;

tf_item_declaration
  : block_item_declaration
  | tf_port_declaration
  ;

tf_port_list: tf_port_item (COMMA tf_port_item)*;

tf_port_item
  : attribute_instance* tf_port_direction? var_type? data_type_or_implicit identifier
      variable_dimension* (ASSIGN_OP expression)?
  ;

tf_port_direction: INPUT | OUTPUT | INOUT | REF | CONST REF;

tf_port_declaration
  : attribute_instance* tf_port_direction var_type? data_type_or_implicit
      list_of_tf_variable_identifiers SEMICOLON
  ;

task_prototype
  : TASK identifier (OPEN_PARENS tf_port_list? CLOSE_PARENS)?
  ;

block_item_declaration
  : attribute_instance* (
    data_declaration
    | local_parameter_declaration SEMICOLON
    | parameter_declaration SEMICOLON
    | overload_declaration
    | let_declaration
  )
  ;

overload_declaration
  : BIND overload_operator FUNCTION data_type identifier OPEN_PARENS overload_proto_formals
      CLOSE_PARENS SEMICOLON
  ;

overload_operator
  : PLUS          # OverloadOp_Plus
  | PLUSPLUS      # OverloadOp_PlusPlus
  | MINUS         # OverloadOp_Minus
  | MINUSMINUS    # OverloadOp_MinusMinus
  | STAR          # OverloadOp_Mult
  | STARSTAR      # OverloadOp_StarStar
  | DIV           # OverloadOp_Div
  | PERCENT       # OverloadOp_Percent
  | EQUIV         # OverloadOp_Equiv
  | NOTEQUAL      # OverloadOp_NotEqual
  | LESS          # OverloadOp_Less
  | LESS_EQUAL    # OverloadOp_LessEqual
  | GREATER       # OverloadOp_Greater
  | GREATER_EQUAL # OverloadOp_GreaterEqual
  | ASSIGN_OP     # OverloadOp_Equal
  ;

overload_proto_formals: data_type (COMMA data_type)*;

virtual_interface_declaration
  : VIRTUAL INTERFACE? interface_identifier list_of_virtual_interface_decl SEMICOLON
  ;

modport_item
  : identifier OPEN_PARENS modport_ports_declaration (
    COMMA modport_ports_declaration
  )* CLOSE_PARENS
  ;

modport_ports_declaration
  : attribute_instance* (
    modport_simple_ports_declaration
    | modport_hierarchical_ports_declaration
    | modport_tf_ports_declaration
    | CLOCKING identifier
  )
  ;

modport_simple_ports_declaration
  : port_direction modport_simple_port (
    COMMA modport_simple_port
  )*
  ;

modport_simple_port
  : identifier
  | DOT identifier OPEN_PARENS expression* CLOSE_PARENS
  ;

modport_hierarchical_ports_declaration
  : identifier (OPEN_BRACKET constant_expression CLOSE_BRACKET)? DOT identifier
  ;

modport_tf_ports_declaration
  : (IMPORT | EXPORT) modport_tf_port (COMMA modport_tf_port)*
  ;

modport_tf_port: method_prototype | identifier;

concurrent_assertion_item
  : (identifier COLON)? concurrent_assertion_statement
  | checker_instantiation
  ;

concurrent_assertion_statement
  : assert_property_statement
  | assume_property_statement
  | cover_property_statement
  | cover_sequence_statement
  | restrict_property_statement
  ;

assert_property_statement
  : ASSERT PROPERTY OPEN_PARENS property_spec CLOSE_PARENS action_block
  ;

assume_property_statement
  : ASSUME PROPERTY OPEN_PARENS property_spec CLOSE_PARENS action_block
  ;

cover_property_statement
  : COVER PROPERTY OPEN_PARENS property_spec CLOSE_PARENS statement_or_null
  ;

expect_property_statement
  : EXPECT OPEN_PARENS property_spec CLOSE_PARENS action_block
  ;

cover_sequence_statement
  : COVER SEQUENCE OPEN_PARENS clocking_event? (
    DISABLE IFF OPEN_PARENS expression_or_dist CLOSE_PARENS
  )? sequence_expr CLOSE_PARENS statement_or_null
  ;

restrict_property_statement
  : RESTRICT PROPERTY OPEN_PARENS property_spec CLOSE_PARENS SEMICOLON
  ;

property_instance
  : ps_or_hierarchical_sequence_identifier (
    OPEN_PARENS actual_arg_list? CLOSE_PARENS
  )?
  ;

property_actual_arg: property_expr | sequence_actual_arg;

concurrent_assertion_item_declaration
  : property_declaration
  | sequence_declaration
  ;

assertion_item_declaration
  : property_declaration
  | sequence_declaration
  | let_declaration
  ;

property_declaration
  : PROPERTY identifier (
    OPEN_PARENS property_port_list? CLOSE_PARENS
  )? SEMICOLON assertion_variable_declaration* property_spec SEMICOLON? ENDPROPERTY (
    COLON identifier
  )?
  ;

property_port_list
  : property_port_item (COMMA property_port_item)*
  ;

property_port_item
  : attribute_instance* (LOCAL property_lvar_port_direction?)? property_formal_type identifier
      variable_dimension* (ASSIGN_OP property_actual_arg)?
  ;

property_lvar_port_direction: INPUT;

property_formal_type: sequence_formal_type | PROPERTY;

property_spec
  : clocking_event? (
    DISABLE IFF OPEN_PARENS expression_or_dist CLOSE_PARENS
  )? property_expr
  ;

property_expr
  : sequence_expr
  | STRONG OPEN_PARENS sequence_expr CLOSE_PARENS
  | WEAK OPEN_PARENS sequence_expr CLOSE_PARENS
  | OPEN_PARENS property_expr CLOSE_PARENS
  | NOT property_expr
  | property_expr OR property_expr
  | property_expr AND property_expr
  | sequence_expr OVERLAP_IMPLY property_expr
  | sequence_expr NON_OVERLAP_IMPLY property_expr
  | IF OPEN_PARENS expression_or_dist CLOSE_PARENS property_expr (
    ELSE property_expr
  )?
  | CASE OPEN_PARENS expression_or_dist CLOSE_PARENS property_case_item property_case_item* ENDCASE
  | sequence_expr OVERLAPPED property_expr
  | sequence_expr NONOVERLAPPED property_expr
  | NEXTTIME property_expr
  | NEXTTIME OPEN_BRACKET constant_expression CLOSE_BRACKET property_expr
  | S_NEXTTIME property_expr
  | S_NEXTTIME OPEN_BRACKET constant_expression CLOSE_BRACKET property_expr
  | ALWAYS property_expr
  | ALWAYS OPEN_BRACKET cycle_delay_const_range_expression CLOSE_BRACKET property_expr
  | S_ALWAYS OPEN_BRACKET constant_range CLOSE_BRACKET property_expr
  | S_EVENTUALLY property_expr
  | EVENTUALLY OPEN_BRACKET constant_range CLOSE_BRACKET property_expr
  | S_EVENTUALLY OPEN_BRACKET cycle_delay_const_range_expression CLOSE_BRACKET property_expr
  | property_expr UNTIL property_expr
  | property_expr S_UNTIL property_expr
  | property_expr UNTIL_WITH property_expr
  | property_expr S_UNTIL_WITH property_expr
  | property_expr IMPLIES property_expr
  | property_expr IFF property_expr
  | ACCEPT_ON OPEN_PARENS expression_or_dist CLOSE_PARENS property_expr
  | REJECT_ON OPEN_PARENS expression_or_dist CLOSE_PARENS property_expr
  | SYNC_ACCEPT_ON OPEN_PARENS expression_or_dist CLOSE_PARENS property_expr
  | SYNC_REJECT_ON OPEN_PARENS expression_or_dist CLOSE_PARENS property_expr
  | property_instance
  | clocking_event property_expr
  ;

property_case_item
  : expression_or_dist (COMMA expression_or_dist)* COLON property_expr SEMICOLON?
  | DEFAULT COLON? property_expr SEMICOLON?
  ;

sequence_declaration
  : SEQUENCE identifier (
    OPEN_PARENS sequence_port_list? CLOSE_PARENS
  )? SEMICOLON assertion_variable_declaration* sequence_expr SEMICOLON? ENDSEQUENCE (
    COLON identifier
  )?
  ;

sequence_expr
  : cycle_delay_range sequence_expr (
    cycle_delay_range sequence_expr
  )*
  | sequence_expr cycle_delay_range sequence_expr (
    cycle_delay_range sequence_expr
  )*
  | expression_or_dist boolean_abbrev?
  | OPEN_PARENS expression_or_dist (COMMA sequence_match_item)* CLOSE_PARENS boolean_abbrev?
  | sequence_instance consecutive_repetition?
  | OPEN_PARENS sequence_expr (COMMA sequence_match_item)* CLOSE_PARENS consecutive_repetition?
  | sequence_expr AND sequence_expr
  | sequence_expr INTERSECT sequence_expr
  | sequence_expr OR sequence_expr
  | FIRST_MATCH OPEN_PARENS sequence_expr (
    COMMA sequence_match_item
  )* CLOSE_PARENS
  | expression_or_dist THROUGHOUT sequence_expr
  | sequence_expr WITHIN sequence_expr
  | clocking_event sequence_expr
  ;

cycle_delay_range
  : POUNDPOUND constant_primary
  | Pound_Pound_delay
  | POUNDPOUND OPEN_BRACKET cycle_delay_const_range_expression CLOSE_BRACKET
  | POUNDPOUND ASSOCIATIVE_UNSPECIFIED
  | POUNDPOUND OPEN_BRACKET PLUS CLOSE_BRACKET
  ;

sequence_method_call: sequence_instance DOT identifier;

sequence_match_item
  : operator_assignment
  | inc_or_dec_expression
  | subroutine_call
  ;

sequence_port_list
  : sequence_port_item (COMMA sequence_port_item)*
  ;

sequence_port_item
  : attribute_instance* (LOCAL sequence_lvar_port_direction?)? sequence_formal_type identifier
      variable_dimension* (ASSIGN_OP sequence_actual_arg)?
  ;

sequence_lvar_port_direction
  : INPUT  # SeqLvarPortDir_Input
  | INOUT  # SeqLvarPortDir_Inout
  | OUTPUT # SeqLvarPortDir_Output
  ;

sequence_formal_type
  : data_type_or_implicit # SeqFormatType_Data
  | SEQUENCE              # SeqFormatType_Sequence
  | UNTYPED               # SeqFormatType_Untyped
  ;

sequence_instance
  : ps_or_hierarchical_sequence_identifier (
    OPEN_PARENS sequence_list_of_arguments CLOSE_PARENS
  )?
  ;

sequence_arg: sequence_actual_arg?;

sequence_list_of_arguments
  : sequence_actual_arg? (COMMA sequence_arg)* (
    COMMA DOT identifier OPEN_PARENS sequence_actual_arg? CLOSE_PARENS
  )*
  | DOT identifier OPEN_PARENS sequence_actual_arg? CLOSE_PARENS (
    COMMA DOT identifier OPEN_PARENS sequence_actual_arg? CLOSE_PARENS
  )*
  ;

sequence_actual_arg: event_expression | sequence_expr;

actual_arg_list
  : actual_arg_expr (COMMA actual_arg_expr)*
  | DOT identifier OPEN_PARENS actual_arg_expr CLOSE_PARENS (
    COMMA DOT identifier OPEN_PARENS actual_arg_expr CLOSE_PARENS
  )*
  ;

actual_arg_expr: event_expression | dollar_keyword;

boolean_abbrev
  : consecutive_repetition
  | non_consecutive_repetition
  | goto_repetition
  ;

consecutive_repetition
  : CONSECUTIVE_REP const_or_range_expression CLOSE_BRACKET
  | ASSOCIATIVE_UNSPECIFIED
  | OPEN_BRACKET PLUS CLOSE_BRACKET
  ;

non_consecutive_repetition
  : NON_CONSECUTIVE_REP const_or_range_expression CLOSE_BRACKET
  ;

goto_repetition
  : GOTO_REP const_or_range_expression CLOSE_BRACKET
  ;

const_or_range_expression
  : constant_expression
  | cycle_delay_const_range_expression
  ;

cycle_delay_const_range_expression
  : constant_expression COLON constant_expression
  | constant_expression COLON DOLLAR
  ;

expression_or_dist
  : expression (DIST OPEN_CURLY dist_list CLOSE_CURLY)?
  ;

assertion_variable_declaration
  : data_type list_of_variable_identifiers SEMICOLON
  ;

let_declaration
  : LET identifier (OPEN_PARENS let_port_list? CLOSE_PARENS)? ASSIGN_OP expression SEMICOLON
  ;

let_port_list: let_port_item (COMMA let_port_item)*;

let_port_item
  : attribute_instance* let_formal_type identifier variable_dimension* (
    ASSIGN_OP expression
  )?
  ;

let_formal_type: data_type_or_implicit | UNTYPED;

/*
 let_expression :
 package_scope? identifier (OPEN_PARENS list_of_arguments CLOSE_PARENS)? ;
 */

covergroup_declaration
  : COVERGROUP identifier (
    OPEN_PARENS tf_port_list? CLOSE_PARENS
  )? coverage_event? SEMICOLON coverage_spec_or_option* ENDGROUP (
    COLON identifier
  )?
  ;

coverage_spec_or_option
  : attribute_instance* (
    coverage_spec
    | coverage_option SEMICOLON
  )
  ;

coverage_option
  : OPTION_DOT identifier ASSIGN_OP expression
  | TYPE_OPTION_DOT identifier ASSIGN_OP expression
  ;

coverage_spec: cover_point | cover_cross;

coverage_event
  : clocking_event
  | WITH FUNCTION SAMPLE OPEN_PARENS tf_port_list? CLOSE_PARENS
  | ATAT OPEN_PARENS block_event_expression CLOSE_PARENS
  ;

block_event_expression
  : block_event_expression OR block_event_expression
  | BEGIN hierarchical_btf_identifier
  | END hierarchical_btf_identifier
  ;

hierarchical_btf_identifier
  : hierarchical_identifier
  | dollar_root_keyword? identifier (
    (OPEN_BRACKET constant_expression CLOSE_BRACKET)* DOT identifier
  )* class_scope? identifier
  ;

cover_point
  : (data_type_or_implicit identifier COLON)? COVERPOINT expression (
    IFF OPEN_PARENS expression CLOSE_PARENS
  )? bins_or_empty
  ;

bins_or_empty
  : OPEN_CURLY attribute_instance* (bins_or_options SEMICOLON)* CLOSE_CURLY
  | SEMICOLON
  ;

bins_or_options
  : coverage_option
  | WILDCARD? bins_keyword identifier (
    OPEN_BRACKET expression? CLOSE_BRACKET
  )? ASSIGN_OP OPEN_CURLY range_list CLOSE_CURLY (
    WITH OPEN_PARENS expression CLOSE_PARENS
  )? (IFF OPEN_PARENS expression CLOSE_PARENS)?
  | WILDCARD? bins_keyword identifier (
    OPEN_BRACKET expression? CLOSE_BRACKET
  )? ASSIGN_OP identifier (
    WITH OPEN_PARENS expression CLOSE_PARENS
  )? (IFF OPEN_PARENS expression CLOSE_PARENS)?
  | WILDCARD? bins_keyword identifier (
    OPEN_BRACKET expression? CLOSE_BRACKET
  )? ASSIGN_OP expression (
    IFF OPEN_PARENS expression CLOSE_PARENS
  )?
  | WILDCARD? bins_keyword identifier unsized_dimension? ASSIGN_OP trans_list (
    IFF OPEN_PARENS expression CLOSE_PARENS
  )?
  | bins_keyword identifier (
    OPEN_BRACKET expression? CLOSE_BRACKET
  )? ASSIGN_OP DEFAULT (IFF OPEN_PARENS expression CLOSE_PARENS)?
  | bins_keyword identifier ASSIGN_OP DEFAULT SEQUENCE (
    IFF OPEN_PARENS expression CLOSE_PARENS
  )?
  ;

bins_keyword
  : BINS         # Bins_Bins
  | ILLEGAL_BINS # Bins_Illegal
  | IGNORE_BINS  # Bins_Ignore
  ;

range_list: value_range (COMMA value_range)*;

trans_list
  : OPEN_PARENS trans_set CLOSE_PARENS (
    COMMA OPEN_PARENS trans_set CLOSE_PARENS
  )*
  ;

trans_set: trans_range_list (TRANSITION_OP trans_range_list)*;

trans_range_list
  : range_list
  | range_list CONSECUTIVE_REP repeat_range CLOSE_BRACKET
  | range_list GOTO_REP repeat_range CLOSE_BRACKET
  | range_list NON_CONSECUTIVE_REP repeat_range CLOSE_BRACKET
  ;

repeat_range: expression | expression COLON expression;

cover_cross
  : (identifier COLON)? CROSS list_of_cross_items (
    IFF OPEN_PARENS expression CLOSE_PARENS
  )? cross_body
  ;

list_of_cross_items
  : cross_item COMMA cross_item (COMMA cross_item)*
  ;

cross_item: identifier;

cross_body: OPEN_CURLY cross_body_item* CLOSE_CURLY | SEMICOLON;

cross_body_item
  : function_declaration
  | bins_selection_or_option SEMICOLON
  ;

bins_selection_or_option
  : attribute_instance* (coverage_option | bins_selection)
  ;

bins_selection
  : bins_keyword identifier ASSIGN_OP select_expression (
    IFF OPEN_PARENS expression CLOSE_PARENS
  )?
  ;

select_expression
  : select_condition
  | BANG select_condition
  | select_expression (LOGICAL_AND | LOGICAL_OR) select_expression
  | OPEN_PARENS select_expression CLOSE_PARENS
  | select_expression WITH OPEN_PARENS expression CLOSE_PARENS (
    matches expression
  )?
  | identifier
  | expression (matches expression)?
  ;

select_condition
  : BINSOF OPEN_PARENS bins_expression CLOSE_PARENS (
    INTERSECT OPEN_CURLY open_range_list CLOSE_CURLY
  )?
  ;

bins_expression: identifier (DOT identifier)?;

open_range_list: value_range (COMMA value_range)*;

gate_instantiation
  : cmos_switchtype delay3? cmos_switch_instance (
    COMMA cmos_switch_instance
  )* SEMICOLON
  | enable_gatetype drive_strength? delay3? enable_gate_instance (
    COMMA enable_gate_instance
  )* SEMICOLON
  | mos_switchtype delay3? mos_switch_instance (
    COMMA mos_switch_instance
  )* SEMICOLON
  | n_input_gatetype drive_strength? delay2? n_input_gate_instance (
    COMMA n_input_gate_instance
  )* SEMICOLON
  | n_output_gatetype drive_strength? delay2? n_output_gate_instance (
    COMMA n_output_gate_instance
  )* SEMICOLON
  | pass_en_switchtype delay2? pass_enable_switch_instance (
    COMMA pass_enable_switch_instance
  )* SEMICOLON
  | pass_switchtype pass_switch_instance (
    COMMA pass_switch_instance
  )* SEMICOLON
  | PULLDOWN pulldown_strength? pull_gate_instance (
    COMMA pull_gate_instance
  )* SEMICOLON
  | PULLUP pullup_strength? pull_gate_instance (
    COMMA pull_gate_instance
  )* SEMICOLON
  ;

cmos_switch_instance
  : name_of_instance? OPEN_PARENS net_lvalue COMMA expression COMMA expression COMMA expression
      CLOSE_PARENS
  ;

enable_gate_instance
  : name_of_instance? OPEN_PARENS net_lvalue COMMA expression COMMA expression CLOSE_PARENS
  ;

mos_switch_instance
  : name_of_instance? OPEN_PARENS net_lvalue COMMA expression COMMA expression CLOSE_PARENS
  ;

n_input_gate_instance
  : name_of_instance? OPEN_PARENS net_lvalue COMMA expression (
    COMMA expression
  )* CLOSE_PARENS
  ;

n_output_gate_instance
  : name_of_instance? OPEN_PARENS net_lvalue (COMMA net_lvalue)* COMMA expression CLOSE_PARENS
  ;

pass_switch_instance
  : name_of_instance? OPEN_PARENS net_lvalue COMMA net_lvalue CLOSE_PARENS
  ;

pass_enable_switch_instance
  : name_of_instance? OPEN_PARENS net_lvalue COMMA net_lvalue COMMA expression CLOSE_PARENS
  ;

pull_gate_instance
  : name_of_instance? OPEN_PARENS net_lvalue CLOSE_PARENS
  ;

pulldown_strength
  : OPEN_PARENS strength0 COMMA strength1 CLOSE_PARENS
  | OPEN_PARENS strength1 COMMA strength0 CLOSE_PARENS
  | OPEN_PARENS strength0 CLOSE_PARENS
  ;

pullup_strength
  : OPEN_PARENS strength0 COMMA strength1 CLOSE_PARENS
  | OPEN_PARENS strength1 COMMA strength0 CLOSE_PARENS
  | OPEN_PARENS strength1 CLOSE_PARENS
  ;

cmos_switchtype
  : CMOS  # CmosSwitchType_Cmos
  | RCMOS # CmosSwitchType_RCmos
  ;

enable_gatetype
  : BUFIF0 # EnableGateType_Bufif0
  | BUFIF1 # EnableGateType_Bufif1
  | NOTIF0 # EnableGateType_Notif0
  | NOTIF1 # EnableGateType_Notif1
  ;

mos_switchtype
  : NMOS  # MosSwitchType_NMos
  | PMOS  # MosSwitchType_PMos
  | RNMOS # MosSwitchType_RNMos
  | RPMOS # MosSwitchType_RPMos
  ;

n_input_gatetype
  : AND  # NInpGate_And
  | NAND # NInpGate_Nand
  | OR   # NInpGate_Or
  | NOR  # NInpGate_Nor
  | XOR  # NInpGate_Xor
  | XNOR # NInpGate_Xnor
  ;

n_output_gatetype: BUF # NOutGate_Buf | NOT # NOutGate_Not;

pass_en_switchtype
  : TRANIF0  # PassEnSwitch_Tranif0
  | TRANIF1  # PassEnSwitch_Tranif1
  | RTRANIF1 # PassEnSwitch_RTranif1
  | RTRANIF0 # PassEnSwitch_RTranif0
  ;

pass_switchtype
  : TRAN  # PassSwitch_Tran
  | RTRAN # PassSwitch_RTran
  ;

module_instantiation
  : identifier parameter_value_assignment? hierarchical_instance (
    COMMA hierarchical_instance
  )* SEMICOLON
  ;

parameter_value_assignment
  : POUND (
    OPEN_PARENS list_of_parameter_assignments? CLOSE_PARENS
  )
  | Pound_delay
  | POUND Simple_identifier
  ;

list_of_parameter_assignments
  : ordered_parameter_assignment (
    COMMA ordered_parameter_assignment
  )*
  | named_parameter_assignment (COMMA named_parameter_assignment)*
  ;

ordered_parameter_assignment: param_expression;

named_parameter_assignment
  : DOT identifier OPEN_PARENS param_expression? CLOSE_PARENS
  ;

hierarchical_instance
  : name_of_instance OPEN_PARENS list_of_port_connections CLOSE_PARENS
  ;

name_of_instance: identifier unpacked_dimension*;

list_of_port_connections
  : ordered_port_connection (COMMA ordered_port_connection)*
  | named_port_connection (COMMA named_port_connection)*
  ;

ordered_port_connection: attribute_instance* expression?;

named_port_connection
  : attribute_instance* (
    DOT identifier (OPEN_PARENS expression? CLOSE_PARENS)?
    | DOTSTAR
  )
  ;

checker_instantiation
  : ps_identifier name_of_instance OPEN_PARENS list_of_checker_port_connections CLOSE_PARENS SEMICOLON
  ;

list_of_checker_port_connections
  : ordered_checker_port_connection (
    COMMA ordered_checker_port_connection
  )?
  | named_checker_port_connection (
    COMMA named_checker_port_connection
  )?
  ;

ordered_checker_port_connection
  : attribute_instance* property_actual_arg?
  ;

named_checker_port_connection
  : attribute_instance* (
    DOT identifier (
      OPEN_PARENS property_actual_arg? CLOSE_PARENS
    )?
    | DOTSTAR
  )
  ;

generated_module_instantiation
  : GENERATE generate_module_item* ENDGENERATE
  ;

generate_module_item
  : generate_module_conditional_statement
  | generate_module_case_statement
  | generate_module_loop_statement
  | (identifier COLON)? generate_module_block
  | module_or_generate_item
  ;

generate_module_conditional_statement
  : IF OPEN_PARENS constant_expression CLOSE_PARENS generate_module_item (
    ELSE generate_module_item
  )?
  ;

generate_module_case_statement
  : CASE OPEN_PARENS constant_expression CLOSE_PARENS genvar_module_case_item
      genvar_module_case_item* ENDCASE
  ;

genvar_module_case_item
  : constant_expression (COMMA constant_expression)* COLON generate_module_item
  | DEFAULT COLON? generate_module_item
  ;

generate_module_loop_statement
  : FOR OPEN_PARENS genvar_decl_assignment SEMICOLON constant_expression SEMICOLON genvar_assignment
      CLOSE_PARENS generate_module_named_block
  ;

genvar_assignment
  : identifier assignment_operator constant_expression
  | inc_or_dec_operator identifier
  | identifier inc_or_dec_operator
  ;

genvar_decl_assignment
  : GENVAR? identifier ASSIGN_OP constant_expression
  ;

generate_module_named_block
  : BEGIN COLON identifier generate_module_item* END (
    COLON identifier
  )?
  | identifier COLON generate_module_block
  ;

generate_module_block
  : BEGIN (COLON identifier)? generate_module_item* END (
    COLON identifier
  )?
  ;

generated_interface_instantiation
  : GENERATE generate_interface_item* ENDGENERATE
  ;

generate_interface_item
  : generate_interface_conditional_statement
  | generate_interface_case_statement
  | generate_interface_loop_statement
  | (identifier COLON) generate_interface_block
  | interface_or_generate_item
  ;

generate_interface_conditional_statement
  : IF OPEN_PARENS constant_expression CLOSE_PARENS generate_interface_item (
    ELSE generate_interface_item
  )?
  ;

generate_interface_case_statement
  : CASE OPEN_PARENS constant_expression CLOSE_PARENS genvar_interface_case_item
      genvar_interface_case_item* ENDCASE
  ;

genvar_interface_case_item
  : constant_expression (COMMA constant_expression)* COLON generate_interface_item
  | DEFAULT COLON? generate_interface_item
  ;

generate_interface_loop_statement
  : FOR OPEN_PARENS genvar_decl_assignment SEMICOLON constant_expression SEMICOLON genvar_assignment
      CLOSE_PARENS generate_interface_named_block
  ;

generate_interface_named_block
  : BEGIN COLON identifier generate_interface_item* END (
    COLON identifier
  )?
  | identifier COLON generate_interface_block
  ;

generate_interface_block
  : BEGIN (COLON identifier)? generate_interface_item* END (
    COLON identifier
  )?
  ;

generate_region: GENERATE generate_item* ENDGENERATE;

loop_generate_construct
  : FOR OPEN_PARENS genvar_initialization SEMICOLON constant_expression SEMICOLON genvar_iteration
      CLOSE_PARENS generate_item
  ;

genvar_initialization
  : GENVAR? identifier ASSIGN_OP constant_expression
  ;

genvar_iteration
  : identifier assignment_operator constant_expression
  | inc_or_dec_operator identifier
  | identifier inc_or_dec_operator
  ;

conditional_generate_construct
  : if_generate_construct
  | case_generate_construct
  ;

if_generate_construct
  : IF OPEN_PARENS constant_expression CLOSE_PARENS generate_item 
    ( ELSE generate_item  | {_input->LA(1) != ELSE}? );

case_generate_construct
  : CASE OPEN_PARENS constant_expression CLOSE_PARENS (case_generate_item)+ ENDCASE
  ;

case_generate_item
  : constant_expression (COMMA constant_expression)* COLON generate_item
  | DEFAULT COLON? generate_item
  ;

generate_begin_end_block:
 ( identifier COLON )? BEGIN ( COLON identifier | {_input->LA(1) != COLON}? )
        ( generate_item )*
    END ( COLON identifier | {_input->LA(1) != COLON}? )
  ;

//generate_item
// : {isModuleGenerator($ctx)}? module_or_generate_item | {isInterfaceGenerator($ctx)}?
// interface_or_generate_item | {isCheckerGenerator($ctx)}? (checker_or_generate_item_declaration |
// generate_region) ;

generate_item
  : module_or_generate_item
  | attribute_instance* (
    MODPORT modport_item (COMMA modport_item)* SEMICOLON
    | extern_tf_declaration
  )
  | checker_or_generate_item_declaration
  | generate_region
  | generate_begin_end_block
  ;

udp_nonansi_declaration
  : attribute_instance* PRIMITIVE identifier OPEN_PARENS udp_port_list CLOSE_PARENS SEMICOLON
  ;

udp_ansi_declaration
  : attribute_instance* PRIMITIVE identifier OPEN_PARENS udp_declaration_port_list CLOSE_PARENS
      SEMICOLON
  ;

udp_declaration
  : udp_nonansi_declaration udp_port_declaration udp_port_declaration* udp_body ENDPRIMITIVE (
    COLON identifier
  )?
  | udp_ansi_declaration udp_body ENDPRIMITIVE (COLON identifier)?
  | EXTERN udp_nonansi_declaration
  | EXTERN udp_ansi_declaration
  | attribute_instance* PRIMITIVE identifier OPEN_PARENS DOTSTAR CLOSE_PARENS SEMICOLON
      udp_port_declaration* udp_body ENDPRIMITIVE (
    COLON identifier
  )?
  ;

udp_port_list: identifier COMMA identifier (COMMA identifier)*;

udp_declaration_port_list
  : udp_output_declaration COMMA udp_input_declaration (
    COMMA udp_input_declaration
  )*
  ;

udp_port_declaration
  : udp_output_declaration SEMICOLON
  | udp_input_declaration SEMICOLON
  | udp_reg_declaration SEMICOLON
  ;

udp_output_declaration
  : attribute_instance* (
    OUTPUT identifier
    | OUTPUT REG identifier (ASSIGN_OP constant_expression)?
  )
  ;

udp_input_declaration
  : attribute_instance* INPUT identifier_list
  ;

udp_reg_declaration: attribute_instance* REG identifier;

udp_body: combinational_body | sequential_body;

combinational_body
  : TABLE combinational_entry combinational_entry* ENDTABLE
  ;

combinational_entry
  : level_input_list COLON output_symbol SEMICOLON
  ;

sequential_body
  : udp_initial_statement? TABLE sequential_entry sequential_entry* ENDTABLE
  ;

udp_initial_statement
  : INITIAL identifier ASSIGN_OP init_val SEMICOLON
  ;

init_val
  : ONE_TICK_b0     # InitVal_1Tickb0
  | ONE_TICK_b1     # InitVal_1Tickb1
  | ONE_TICK_B0     # InitVal_1TickB0
  | ONE_TICK_B1     # InitVal_1TickB1
  | ONE_TICK_bx     # InitVal_1Tickbx
  | ONE_TICK_bX     # InitVal_1TickbX
  | ONE_TICK_Bx     # InitVal_1TickBx
  | ONE_TICK_BX     # InitVal_1TickBX
  | Integral_number # InitVal_Integral
  ;

sequential_entry
  : seq_input_list COLON level_symbol COLON next_state SEMICOLON
  ;

seq_input_list: level_input_list | edge_input_list;

level_input_list: level_symbol level_symbol*;

edge_input_list: level_symbol* edge_indicator level_symbol*;

edge_indicator
  : OPEN_PARENS /* Will have to check post parse time that there are 2 items (10 becomes one int): */
      level_symbol+ CLOSE_PARENS
  | edge_symbol
  ;

next_state: output_symbol | MINUS;

output_symbol: Integral_number | Simple_identifier;

level_symbol: Integral_number | Simple_identifier | QMARK;

edge_symbol: Simple_identifier | STAR;

udp_instantiation
  : identifier drive_strength? delay2? udp_instance (
    COMMA udp_instance
  )* SEMICOLON
  ;

udp_instance
  : name_of_instance? OPEN_PARENS net_lvalue COMMA expression (
    COMMA expression
  )* CLOSE_PARENS
  ;

continuous_assign
  : ASSIGN drive_strength? delay3? list_of_net_assignments SEMICOLON
  | ASSIGN_OP delay_control? list_of_variable_assignments SEMICOLON
  ;

list_of_net_assignments: net_assignment (COMMA net_assignment)*;

list_of_variable_assignments
  : variable_assignment (COMMA variable_assignment)*
  ;

net_alias: ALIAS net_lvalue (ASSIGN_OP net_lvalue)+ SEMICOLON;

net_assignment: net_lvalue ASSIGN_OP expression;

initial_construct: INITIAL statement_or_null;

always_construct: always_keyword statement;

always_keyword: ALWAYS | ALWAYS_COMB | ALWAYS_LATCH | ALWAYS_FF;

blocking_assignment
  : variable_lvalue ASSIGN_OP delay_or_event_control expression
  | nonrange_variable_lvalue ASSIGN_OP dynamic_array_new
  | (implicit_class_handle DOT | class_scope | package_scope)? (
    identifier
    | hierarchical_identifier
  ) select ASSIGN_OP class_new
  | operator_assignment
  ;

operator_assignment
  : variable_lvalue assignment_operator expression
  ;

assignment_operator
  : ASSIGN_OP
  | ADD_ASSIGN
  | SUB_ASSIGN
  | MULT_ASSIGN
  | DIV_ASSIGN
  | MODULO_ASSIGN
  | BITW_AND_ASSIGN
  | BITW_OR_ASSIGN
  | BITW_XOR_ASSIGN
  | BITW_LEFT_SHIFT_ASSIGN
  | BITW_RIGHT_SHIFT_ASSIGN
  | ARITH_SHIFT_LEFT_ASSIGN
  | ARITH_SHIFT_RIGHT_ASSIGN
  ;

nonblocking_assignment
  : variable_lvalue LESS_EQUAL delay_or_event_control? expression
  ;

procedural_continuous_assignment
  : ASSIGN variable_assignment
  | DEASSIGN variable_lvalue
  | FORCE (variable_assignment | net_assignment)
  | RELEASE (variable_lvalue | net_lvalue)
  ;

variable_assignment: variable_lvalue ASSIGN_OP expression;

action_block
  : statement_or_null
  | statement? ELSE statement_or_null
  ;

seq_block
  : BEGIN (COLON identifier)? block_item_declaration* statement_or_null* END (
    COLON identifier
  )?
  ;

par_block
  : FORK (COLON identifier)? block_item_declaration* statement_or_null* (
    join_keyword
    | join_any_keyword
    | join_none_keyword
  ) (COLON identifier)?
  ;

join_keyword: JOIN;

join_any_keyword: JOIN_ANY;

join_none_keyword: JOIN_NONE;

statement_or_null: statement | attribute_instance* SEMICOLON;

statement
  : (identifier COLON)? attribute_instance* statement_item
  ;

statement_item
  : blocking_assignment SEMICOLON
  | nonblocking_assignment SEMICOLON
  | procedural_continuous_assignment SEMICOLON
  | case_statement
  | conditional_statement
  | inc_or_dec_expression SEMICOLON
  | subroutine_call_statement
  | disable_statement
  | event_trigger
  | loop_statement
  | jump_statement
  | par_block
  | procedural_timing_control_statement
  | seq_block
  | wait_statement
  | procedural_assertion_statement
  // This is covered by assignments (and created ambiguities) | clocking_drive SEMICOLON
  | randsequence_statement
  | randcase_statement
  | expect_property_statement
  | system_task SEMICOLON
  | surelog_macro_not_defined
  ;

function_statement_or_null
  : statement
  | attribute_instance* SEMICOLON
  ;

procedural_timing_control_statement
  : procedural_timing_control statement_or_null
  ;

delay_or_event_control
  : delay_control
  | event_control
  | REPEAT OPEN_PARENS expression CLOSE_PARENS event_control
  ;

delay_control
  : pound_delay_value
  | POUND OPEN_PARENS mintypmax_expression CLOSE_PARENS
  ;

event_control
  : AT OPEN_PARENS event_expression CLOSE_PARENS
  | ATSTAR
  | AT_PARENS_STAR
  | AT ps_or_hierarchical_identifier
  ;

event_expression
  : edge_identifier? expression (IFF expression)?
  | sequence_instance (IFF expression)?
  | event_expression (or_operator | comma_operator) event_expression
  | OPEN_PARENS event_expression CLOSE_PARENS
  ;

or_operator: OR;

comma_operator: COMMA;

procedural_timing_control
  : delay_control
  | event_control
  | cycle_delay
  ;

jump_statement
  : RETURN expression? SEMICOLON
  | BREAK SEMICOLON
  | CONTINUE SEMICOLON
  ;

final_construct: FINAL statement;

wait_statement
  : WAIT (
    (OPEN_PARENS expression CLOSE_PARENS statement_or_null)
    | (FORK SEMICOLON)
  )
  | WAIT_ORDER OPEN_PARENS (identifier | hierarchical_identifier) (
    COMMA (identifier | hierarchical_identifier)
  )* CLOSE_PARENS action_block
  ;

event_trigger
  : IMPLY (identifier | hierarchical_identifier) SEMICOLON
  | NON_BLOCKING_TRIGGER_EVENT_OP delay_or_event_control? (
    identifier
    | hierarchical_identifier
  ) SEMICOLON
  ;

disable_statement
  : DISABLE (identifier | hierarchical_identifier | FORK) SEMICOLON
  ;

conditional_statement
  : unique_priority? IF OPEN_PARENS cond_predicate CLOSE_PARENS statement_or_null (
    ELSE statement_or_null
    | {_input->LA(1) != ELSE}?
  )
  ;

//conditional_statement : unique_priority? IF OPEN_PARENS cond_predicate CLOSE_PARENS
// statement_or_null (ELSE IF OPEN_PARENS cond_predicate CLOSE_PARENS statement_or_null)* (ELSE
// statement_or_null)* ;

unique_priority: UNIQUE | UNIQUE0 | PRIORITY;

cond_predicate
  : expression_or_cond_pattern (
    COND_PRED_OP expression_or_cond_pattern
  )*
  ;

expression_or_cond_pattern: expression (matches pattern)?;

matches: MATCHES;

case_statement
  : unique_priority? case_keyword OPEN_PARENS expression CLOSE_PARENS (
    (case_item case_item*)
    | (MATCHES case_pattern_item case_pattern_item*)
    | (INSIDE case_inside_item case_inside_item*)
  ) ENDCASE
  ;

case_keyword: CASE | CASEZ | CASEX;

case_item
  : expression (COMMA expression)* COLON statement_or_null
  | DEFAULT COLON? statement_or_null
  ;

case_pattern_item
  : pattern (COND_PRED_OP expression)? COLON statement_or_null
  | DEFAULT COLON? statement_or_null
  ;

case_inside_item
  : open_range_list COLON statement_or_null
  | DEFAULT COLON? statement_or_null
  ;

randcase_statement
  : RANDCASE randcase_item randcase_item* ENDCASE
  ;

randcase_item: expression COLON statement_or_null;

pattern
  : DOT identifier
  | DOTSTAR
  | constant_expression
  | TAGGED identifier pattern?
  | TICK OPEN_CURLY pattern (COMMA pattern)* CLOSE_CURLY
  | TICK OPEN_CURLY identifier COLON pattern (
    COMMA identifier COLON pattern
  )* CLOSE_CURLY
  ;

assignment_pattern
  : TICK OPEN_CURLY expression (COMMA expression)* CLOSE_CURLY
  | TICK OPEN_CURLY structure_pattern_key COLON expression (
    COMMA structure_pattern_key COLON expression
  )* CLOSE_CURLY
  | TICK OPEN_CURLY array_pattern_key COLON expression (
    COMMA array_pattern_key COLON expression
  )* CLOSE_CURLY
  // | TICK OPEN_CURLY constant_expression OPEN_CURLY expression (COMMA expression)* CLOSE_CURLY CLOSE_CURLY
  | TICK OPEN_CURLY constant_expression OPEN_CURLY expression (
    (CLOSE_CURLY (COMMA expression)*)
    | ((COMMA expression)* CLOSE_CURLY)
  ) CLOSE_CURLY
  | TICK OPEN_CURLY CLOSE_CURLY
  ;

structure_pattern_key: identifier | assignment_pattern_key;

array_pattern_key: constant_expression | assignment_pattern_key;

assignment_pattern_key: simple_type | DEFAULT;

assignment_pattern_expression
  : assignment_pattern_expression_type? assignment_pattern
  ;

assignment_pattern_expression_type
  : ps_type_identifier
  | ps_identifier
  | integer_atom_type
  | type_reference
  ;

constant_assignment_pattern_expression
  : assignment_pattern_expression
  ;

assignment_pattern_net_lvalue
  : TICK OPEN_CURLY net_lvalue (COMMA net_lvalue)* CLOSE_CURLY
  ;

assignment_pattern_variable_lvalue
  : TICK OPEN_CURLY variable_lvalue (COMMA variable_lvalue)* CLOSE_CURLY
  ;

loop_statement
  : FOREVER statement_or_null
  | (REPEAT | WHILE) OPEN_PARENS expression CLOSE_PARENS statement_or_null
  | FOR OPEN_PARENS for_initialization? SEMICOLON expression? SEMICOLON for_step? CLOSE_PARENS
      statement_or_null
  | DO statement_or_null WHILE OPEN_PARENS expression CLOSE_PARENS SEMICOLON
  | FOREACH OPEN_PARENS ps_or_hierarchical_array_identifier OPEN_BRACKET loop_variables
      CLOSE_BRACKET (OPEN_BRACKET identifier CLOSE_BRACKET)? CLOSE_PARENS statement
  ;

for_initialization
  : list_of_variable_assignments
  | for_variable_declaration (COMMA for_variable_declaration)*
  ;

for_variable_declaration
  : VAR? data_type identifier ASSIGN_OP expression (
    COMMA identifier ASSIGN_OP expression
  )*
  ;

for_step: for_step_assignment (COMMA for_step_assignment)*;

for_step_assignment
  : operator_assignment
  | inc_or_dec_expression
  | subroutine_call
  ;

comma: COMMA;

loop_variables: identifier? (comma identifier?)*;

subroutine_call_statement
  : subroutine_call SEMICOLON
  | VOID TICK OPEN_PARENS subroutine_call CLOSE_PARENS SEMICOLON
  ;

assertion_item
  : concurrent_assertion_item
  | deferred_immediate_assertion_item
  ;

deferred_immediate_assertion_item
  : (identifier COLON)? deferred_immediate_assertion_statement
  ;

procedural_assertion_statement
  : concurrent_assertion_statement
  | immediate_assertion_statement
  | checker_instantiation
  ;

immediate_assertion_statement
  : simple_immediate_assertion_statement
  | deferred_immediate_assertion_statement
  ;

simple_immediate_assertion_statement
  : simple_immediate_assert_statement
  | simple_immediate_assume_statement
  | simple_immediate_cover_statement
  ;

simple_immediate_assert_statement
  : ASSERT OPEN_PARENS expression CLOSE_PARENS action_block
  ;

simple_immediate_assume_statement
  : ASSUME OPEN_PARENS expression CLOSE_PARENS action_block
  ;

simple_immediate_cover_statement
  : COVER OPEN_PARENS expression CLOSE_PARENS statement_or_null
  ;

deferred_immediate_assertion_statement
  : deferred_immediate_assert_statement
  | deferred_immediate_assume_statement
  | deferred_immediate_cover_statement
  ;

deferred_immediate_assert_statement
  : ASSERT (Pound_Pound_delay | Pound_delay) OPEN_PARENS expression CLOSE_PARENS action_block
  | ASSERT FINAL (expression) action_block
  ;

deferred_immediate_assume_statement
  : ASSUME (Pound_Pound_delay | Pound_delay) OPEN_PARENS expression CLOSE_PARENS action_block
  | ASSUME FINAL OPEN_PARENS expression CLOSE_PARENS action_block
  ;

deferred_immediate_cover_statement
  : COVER (Pound_Pound_delay | Pound_delay) OPEN_PARENS expression CLOSE_PARENS statement_or_null
  | COVER FINAL OPEN_PARENS expression CLOSE_PARENS statement_or_null
  ;

clocking_declaration
  : DEFAULT? CLOCKING identifier? clocking_event SEMICOLON clocking_item* ENDCLOCKING (
    COLON identifier
  )?
  | GLOBAL CLOCKING identifier? clocking_event SEMICOLON ENDCLOCKING (
    COLON identifier
  )?
  ;

clocking_event
  : AT identifier
  | AT OPEN_PARENS event_expression CLOSE_PARENS
  ;

clocking_item
  : DEFAULT default_skew SEMICOLON
  | clocking_direction list_of_clocking_decl_assign SEMICOLON
  | attribute_instance* concurrent_assertion_item_declaration
  ;

default_skew
  : INPUT clocking_skew                      # DefaultSkew_Intput
  | OUTPUT clocking_skew                     # DefaultSkew_Output
  | INPUT clocking_skew OUTPUT clocking_skew # DefaultSkew_IntputOutput
  ;

clocking_direction
  : INPUT clocking_skew?                       # ClockingDir_Input
  | OUTPUT clocking_skew?                      # ClockingDir_Output
  | INPUT clocking_skew? OUTPUT clocking_skew? # ClockingDir_InputOutput
  | INOUT                                      # ClockingDir_Inout
  ;

list_of_clocking_decl_assign
  : clocking_decl_assign (COMMA clocking_decl_assign)*
  ;

clocking_decl_assign: identifier (ASSIGN_OP expression)?;

clocking_skew: edge_identifier delay_control? | delay_control;

edge_identifier: POSEDGE | NEGEDGE | EDGE;

clocking_drive
  : clockvar_expression LESS_EQUAL cycle_delay? expression
  | cycle_delay clockvar_expression LESS_EQUAL expression
  ;

cycle_delay
  : POUNDPOUND Integral_number
  | Pound_Pound_delay
  | POUNDPOUND identifier
  | POUNDPOUND OPEN_PARENS expression CLOSE_PARENS
  ;

clockvar
  : dollar_root_keyword? identifier (
    (OPEN_BRACKET constant_expression CLOSE_BRACKET)* DOT identifier
  )*
  ;

clockvar_expression: clockvar select;

randsequence_statement
  : RANDSEQUENCE OPEN_PARENS identifier? CLOSE_PARENS production production* ENDSEQUENCE
  ;

production
  : function_data_type? identifier (
    OPEN_PARENS tf_port_list CLOSE_PARENS
  )? COLON rs_rule (BITW_OR rs_rule)* SEMICOLON
  ;

rs_rule
  : rs_production_list (ASSIGN_VALUE expression rs_code_block?)?
  ;

rs_production_list
  : rs_prod rs_prod*
  | RAND JOIN (OPEN_PARENS expression CLOSE_PARENS)? production_item production_item production_item
      *
  ;

rs_code_block
  : OPEN_CURLY data_declaration* statement_or_null* CLOSE_CURLY
  ;

rs_prod
  : production_item
  | rs_code_block
  | rs_if_else
  | rs_repeat
  | rs_case
  ;

production_item
  : identifier (OPEN_PARENS list_of_arguments CLOSE_PARENS)?
  ;

rs_if_else
  : IF OPEN_PARENS expression CLOSE_PARENS production_item (
    ELSE production_item
  )?
  ;

rs_repeat
  : REPEAT OPEN_PARENS expression CLOSE_PARENS production_item
  ;

rs_case
  : CASE OPEN_PARENS expression CLOSE_PARENS rs_case_item rs_case_item* ENDCASE
  ;

rs_case_item
  : expression (COMMA expression)* COLON production_item
  | DEFAULT COLON? production_item
  ;

specify_block: SPECIFY specify_item* ENDSPECIFY;

specify_item
  : specparam_declaration
  | pulsestyle_declaration
  | showcancelled_declaration
  | path_declaration
  | system_timing_check
  ;

pulsestyle_declaration
  : PULSESTYLE_ONEVENT list_of_path_outputs SEMICOLON
  | PULSESTYLE_ONDETECT list_of_path_outputs SEMICOLON
  ;

showcancelled_declaration
  : SHOWCANCELLED list_of_path_outputs SEMICOLON
  | NOSHOWCANCELLED list_of_path_outputs SEMICOLON
  ;

path_declaration
  : simple_path_declaration SEMICOLON
  | edge_sensitive_path_declaration SEMICOLON
  | state_dependent_path_declaration SEMICOLON
  ;

simple_path_declaration
  : parallel_path_description ASSIGN_OP path_delay_value
  | full_path_description ASSIGN_OP path_delay_value
  ;

parallel_path_description
  : OPEN_PARENS specify_input_terminal_descriptor (PLUS | MINUS)? TRANSITION_OP
      specify_output_terminal_descriptor CLOSE_PARENS
  ;

full_path_description
  : OPEN_PARENS list_of_path_inputs (PLUS | MINUS)? FULL_CONN_OP list_of_path_outputs CLOSE_PARENS
  ;

list_of_path_inputs
  : specify_input_terminal_descriptor (
    COMMA specify_input_terminal_descriptor
  )*
  ;

list_of_path_outputs
  : specify_output_terminal_descriptor (
    COMMA specify_output_terminal_descriptor
  )*
  ;

specify_input_terminal_descriptor
  : (identifier | interface_identifier DOT identifier) (
    OPEN_BRACKET constant_range_expression CLOSE_BRACKET
  )?
  ;

specify_output_terminal_descriptor
  : (identifier | interface_identifier DOT identifier) (
    OPEN_BRACKET constant_range_expression CLOSE_BRACKET
  )?
  ;

path_delay_value
  : list_of_path_delay_expressions
  | OPEN_PARENS list_of_path_delay_expressions CLOSE_PARENS
  ;

list_of_path_delay_expressions
  : t_path_delay_expression
  | trise_path_delay_expression COMMA tfall_path_delay_expression
  | trise_path_delay_expression COMMA tfall_path_delay_expression COMMA tz_path_delay_expression
  | t01_path_delay_expression COMMA t10_path_delay_expression COMMA t0z_path_delay_expression COMMA
      tz1_path_delay_expression COMMA t1z_path_delay_expression COMMA tz0_path_delay_expression
  | t01_path_delay_expression COMMA t10_path_delay_expression COMMA t0z_path_delay_expression COMMA
      tz1_path_delay_expression COMMA t1z_path_delay_expression COMMA tz0_path_delay_expression
      COMMA t0x_path_delay_expression COMMA tx1_path_delay_expression COMMA
      t1x_path_delay_expression COMMA tx0_path_delay_expression COMMA txz_path_delay_expression
      COMMA tzx_path_delay_expression
  ;

t_path_delay_expression: path_delay_expression;
trise_path_delay_expression: path_delay_expression;
tfall_path_delay_expression: path_delay_expression;
tz_path_delay_expression: path_delay_expression;
t01_path_delay_expression: path_delay_expression;
t10_path_delay_expression: path_delay_expression;
t0z_path_delay_expression: path_delay_expression;
tz1_path_delay_expression: path_delay_expression;
t1z_path_delay_expression: path_delay_expression;
tz0_path_delay_expression: path_delay_expression;
t0x_path_delay_expression: path_delay_expression;
tx1_path_delay_expression: path_delay_expression;
t1x_path_delay_expression: path_delay_expression;
tx0_path_delay_expression: path_delay_expression;
txz_path_delay_expression: path_delay_expression;
tzx_path_delay_expression: path_delay_expression;
path_delay_expression: constant_mintypmax_expression;

edge_sensitive_path_declaration
  : parallel_edge_sensitive_path_description ASSIGN_OP path_delay_value
  | full_edge_sensitive_path_description ASSIGN_OP path_delay_value
  ;

parallel_edge_sensitive_path_description
  : OPEN_PARENS edge_identifier? specify_input_terminal_descriptor TRANSITION_OP OPEN_PARENS
      specify_output_terminal_descriptor part_select_op_colon expression CLOSE_PARENS CLOSE_PARENS
  ;

full_edge_sensitive_path_description
  : OPEN_PARENS edge_identifier? list_of_path_inputs FULL_CONN_OP OPEN_PARENS list_of_path_outputs
      part_select_op_colon expression CLOSE_PARENS CLOSE_PARENS
  ;

state_dependent_path_declaration
  : IF OPEN_PARENS module_path_expression CLOSE_PARENS simple_path_declaration
  | IF OPEN_PARENS module_path_expression CLOSE_PARENS edge_sensitive_path_declaration
  | IFNONE simple_path_declaration
  ;

system_timing_check
  : dollar_setup_timing_check
  | dollar_hold_timing_check
  | dollar_setuphold_timing_check
  | dollar_recovery_timing_check
  | dollar_removal_timing_check
  | dollar_recrem_timing_check
  | dollar_skew_timing_check
  | dollar_timeskew_timing_check
  | dollar_fullskew_timing_check
  | dollar_period_timing_check
  | dollar_width_timing_check
  | dollar_nochange_timing_check
  ;

dollar_setup_timing_check
  : DOLLAR Simple_identifier OPEN_PARENS timing_check_event COMMA reference_event COMMA
      timing_check_limit (COMMA notifier?)? CLOSE_PARENS SEMICOLON
  ;

dollar_hold_timing_check
  : DOLLAR Simple_identifier OPEN_PARENS reference_event COMMA timing_check_event COMMA
      timing_check_limit (COMMA notifier?)? CLOSE_PARENS SEMICOLON
  ;

dollar_setuphold_timing_check
  : DOLLAR Simple_identifier OPEN_PARENS reference_event COMMA timing_check_event COMMA
      timing_check_limit COMMA timing_check_limit (
    COMMA notifier? (
      COMMA stamptime_condition? (
        COMMA mintypmax_expression? (
          COMMA delayed_reference? (COMMA delayed_data?)?
        )?
      )?
    )?
  )? CLOSE_PARENS SEMICOLON
  ;

dollar_recovery_timing_check
  : DOLLAR Simple_identifier OPEN_PARENS reference_event COMMA timing_check_event COMMA
      timing_check_limit (COMMA notifier?)? CLOSE_PARENS SEMICOLON
  ;

dollar_removal_timing_check
  : DOLLAR Simple_identifier OPEN_PARENS reference_event COMMA timing_check_event COMMA
      timing_check_limit (COMMA notifier?)? CLOSE_PARENS SEMICOLON
  ;

dollar_recrem_timing_check
  : DOLLAR Simple_identifier OPEN_PARENS reference_event COMMA timing_check_event COMMA
      timing_check_limit COMMA timing_check_limit (
    COMMA notifier? (
      COMMA stamptime_condition? (
        COMMA mintypmax_expression? (
          COMMA delayed_reference? (COMMA delayed_data?)?
        )?
      )?
    )?
  )? CLOSE_PARENS SEMICOLON
  ;

dollar_skew_timing_check
  : DOLLAR Simple_identifier OPEN_PARENS reference_event COMMA timing_check_event COMMA
      timing_check_limit (COMMA notifier?)? CLOSE_PARENS SEMICOLON
  ;

dollar_timeskew_timing_check
  : DOLLAR Simple_identifier OPEN_PARENS reference_event COMMA timing_check_event COMMA
      timing_check_limit (
    COMMA notifier? (
      COMMA event_based_flag? (COMMA remain_active_flag?)?
    )?
  )? CLOSE_PARENS SEMICOLON
  ;

dollar_fullskew_timing_check
  : DOLLAR Simple_identifier OPEN_PARENS reference_event COMMA timing_check_event COMMA
      timing_check_limit COMMA timing_check_limit (
    COMMA notifier? (
      COMMA event_based_flag? (COMMA remain_active_flag?)?
    )?
  )? CLOSE_PARENS SEMICOLON
  ;

dollar_period_timing_check
  : DOLLAR Simple_identifier OPEN_PARENS controlled_timing_check_event COMMA timing_check_limit (
    COMMA notifier?
  )? CLOSE_PARENS SEMICOLON
  ;

dollar_width_timing_check
  : DOLLAR Simple_identifier OPEN_PARENS controlled_timing_check_event COMMA timing_check_limit
      COMMA threshold (COMMA notifier?)? CLOSE_PARENS SEMICOLON
  ;

dollar_nochange_timing_check
  : DOLLAR Simple_identifier OPEN_PARENS reference_event COMMA timing_check_event COMMA
      start_edge_offset COMMA end_edge_offset (COMMA notifier?)? CLOSE_PARENS SEMICOLON
  ;

delayed_data
  : identifier (
    OPEN_BRACKET constant_mintypmax_expression CLOSE_BRACKET
  )?
  ;

delayed_reference
  : identifier (
    OPEN_BRACKET constant_mintypmax_expression CLOSE_BRACKET
  )?
  ;

end_edge_offset: mintypmax_expression;

event_based_flag: constant_expression;

notifier: identifier;

reference_event: timing_check_event;

remain_active_flag: constant_mintypmax_expression;

stamptime_condition: mintypmax_expression;

start_edge_offset: mintypmax_expression;

threshold: constant_expression;

timing_check_limit: mintypmax_expression;

timing_check_event
  : timing_check_event_control? specify_terminal_descriptor (
    COND_PRED_OP timing_check_condition
  )?
  ;

controlled_timing_check_event
  : timing_check_event_control specify_terminal_descriptor (
    COND_PRED_OP timing_check_condition
  )?
  ;

timing_check_event_control
  : POSEDGE                # TimingCheckEventControl_Posedge
  | NEGEDGE                # TimingCheckEventControl_Negedge
  | edge_control_specifier # TimingCheckEventControl_Edge
  ;

specify_terminal_descriptor
  : specify_input_terminal_descriptor
  | specify_output_terminal_descriptor
  ;

edge_control_specifier
  : EDGE OPEN_BRACKET edge_descriptor (COMMA edge_descriptor)* CLOSE_BRACKET
  ;

edge_descriptor
  : Integral_number
  | Simple_identifier Integral_number
  | Integral_number Simple_identifier
  ;
// | Rising | Falling | Simple_identifier Zero_or_one | Zero_or_one Simple_identifier;

timing_check_condition
  : scalar_timing_check_condition
  | OPEN_PARENS scalar_timing_check_condition CLOSE_PARENS
  ;

scalar_timing_check_condition
  : expression
  | TILDA expression
  | expression EQUIV scalar_constant
  | expression FOUR_STATE_LOGIC_EQUAL scalar_constant
  | expression NOTEQUAL scalar_constant
  | expression FOUR_STATE_LOGIC_NOTEQUAL scalar_constant
  ;

scalar_constant
  : ONE_TICK_b0     # Scalar_1Tickb0
  | ONE_TICK_b1     # Scalar_1Tickb1
  | ONE_TICK_B0     # Scalar_1TickB0
  | ONE_TICK_B1     # Scalar_1TickB1
  | TICK_b0         # Scalar_Tickb0
  | TICK_b1         # Scalar_Tickb1
  | TICK_B0         # Scalar_TickB0
  | TICK_B1         # Scalar_TickB1
  | Integral_number # Scalar_Integral
  ;

concatenation
  : OPEN_CURLY expression (COMMA expression)* CLOSE_CURLY
  | OPEN_CURLY array_member_label COLON expression (
    COMMA array_member_label COLON expression
  )* CLOSE_CURLY
  ;

constant_concatenation
  : OPEN_CURLY constant_expression (COMMA constant_expression)* CLOSE_CURLY
  | OPEN_CURLY array_member_label COLON constant_expression (
    COMMA array_member_label COLON constant_expression
  )* CLOSE_CURLY
  ;

array_member_label: DEFAULT | identifier | constant_expression;

constant_multiple_concatenation
  : OPEN_CURLY constant_expression constant_concatenation CLOSE_CURLY
  ;

module_path_concatenation
  : OPEN_CURLY module_path_expression (
    COMMA module_path_expression
  )* CLOSE_CURLY
  ;

module_path_multiple_concatenation
  : OPEN_CURLY constant_expression module_path_concatenation CLOSE_CURLY
  ;

multiple_concatenation
  : OPEN_CURLY expression concatenation CLOSE_CURLY
  ;

streaming_concatenation
  : OPEN_CURLY stream_operator slice_size? stream_concatenation CLOSE_CURLY
  ;

stream_operator: SHIFT_RIGHT | SHIFT_LEFT;

slice_size: simple_type | constant_expression;

stream_concatenation
  : OPEN_CURLY stream_expression (COMMA stream_expression)* CLOSE_CURLY
  ;

stream_expression
  : expression (
    WITH OPEN_BRACKET array_range_expression CLOSE_BRACKET
  )?
  ;

array_range_expression
  : expression
  | expression part_select_op_colon expression
  ;

empty_queue: OPEN_CURLY CLOSE_CURLY;

/*
 subroutine_call
 : tf_call
 | method_call
 | randomize_call
 ;
 */

subroutine_call
  : (
    implicit_class_handle DOT
    | class_scope
    | package_scope
    | dollar_keyword
  )? dollar_root_keyword? identifier (
    constant_bit_select DOT identifier
  )* attribute_instance* (
    (OPEN_PARENS list_of_arguments CLOSE_PARENS)
    | select
  ) (DOT method_call_body)?
  | randomize_call
  ;

argument: expression?;

list_of_arguments
  : expression? (COMMA argument)* (
    COMMA DOT identifier OPEN_PARENS expression? CLOSE_PARENS
  )*
  | DOT identifier OPEN_PARENS expression? CLOSE_PARENS (
    COMMA DOT identifier OPEN_PARENS expression? CLOSE_PARENS
  )*
  ;

method_call
  : method_call_root DOT method_call_body
  | class_type COLONCOLON method_call_body
  ;

method_call_body
  : identifier attribute_instance* (
    OPEN_PARENS list_of_arguments CLOSE_PARENS
  )?
  | built_in_method_call
  ;

built_in_method_call: array_manipulation_call | randomize_call;

array_manipulation_call
  : array_method_name attribute_instance* (
    OPEN_PARENS list_of_arguments CLOSE_PARENS
  )? (WITH OPEN_PARENS expression CLOSE_PARENS)?
  ;

randomize_call
  : RANDOMIZE attribute_instance* (
    OPEN_PARENS (identifier_list | NULL_KEYWORD)? CLOSE_PARENS
  )? (
    WITH (OPEN_PARENS identifier_list? CLOSE_PARENS)? constraint_block
  )?
  ;

method_call_root
  : implicit_class_handle
  | (class_scope | package_scope)? dollar_root_keyword? identifier (
    (OPEN_BRACKET constant_expression CLOSE_BRACKET)* DOT identifier
  )* select
  ;

array_method_name
  : identifier
  | unique_call
  | and_call
  | or_call
  | xor_call
  ;

unique_call: UNIQUE;
and_call: AND;
or_call: OR;
xor_call: XOR;

inc_or_dec_expression
  : inc_or_dec_operator attribute_instance* variable_lvalue
  | variable_lvalue attribute_instance* inc_or_dec_operator
  ;

constant_expression
  : constant_primary
  | (
    PLUS
    | MINUS
    | BANG
    | TILDA
    | BITW_AND
    | BITW_OR
    | BITW_XOR
    | REDUCTION_NAND
    | REDUCTION_NOR
    | REDUCTION_XNOR1
    | REDUCTION_XNOR2
  ) attribute_instance* constant_primary
  | constant_expression STARSTAR attribute_instance* constant_expression
  | constant_expression (STAR | DIV | PERCENT) attribute_instance* constant_expression
  | constant_expression (PLUS | MINUS) attribute_instance* constant_expression
  | constant_expression (
    SHIFT_RIGHT
    | SHIFT_LEFT
    | ARITH_SHIFT_RIGHT
    | ARITH_SHIFT_LEFT
  ) attribute_instance* constant_expression
  | constant_expression (
    LESS
    | LESS_EQUAL
    | GREATER
    | GREATER_EQUAL
    | INSIDE
  ) attribute_instance* constant_expression
  | constant_expression (
    EQUIV
    | NOTEQUAL
    | BINARY_WILDCARD_EQUAL
    | BINARY_WILDCARD_NOTEQUAL
    | FOUR_STATE_LOGIC_EQUAL
    | FOUR_STATE_LOGIC_NOTEQUAL
    | WILD_EQUAL_OP
    | WILD_NOTEQUAL_OP
  ) attribute_instance* constant_expression
  | constant_expression BITW_AND attribute_instance* constant_expression
  | constant_expression (
    REDUCTION_XNOR1
    | REDUCTION_XNOR2
    | REDUCTION_NAND
    | REDUCTION_NOR
    | BITW_XOR
  ) attribute_instance* constant_expression
  | constant_expression BITW_OR attribute_instance* constant_expression
  | constant_expression LOGICAL_AND attribute_instance* constant_expression
  | constant_expression LOGICAL_OR attribute_instance* constant_expression
  | <assoc = right> constant_expression (LOGICAL_AND expression)* conditional_operator
      attribute_instance* expression COLON constant_expression
  | <assoc = right> constant_expression (IMPLY | EQUIVALENCE) attribute_instance*
      constant_expression
  | system_task
  ;

conditional_operator: QMARK;

constant_mintypmax_expression
  : constant_expression (
    COLON constant_expression COLON constant_expression
  )?
  ;

constant_param_expression
  : constant_mintypmax_expression
  | data_type
  | DOLLAR
  ;

param_expression: mintypmax_expression | data_type | DOLLAR;

constant_range_expression
  : constant_expression
  | constant_part_select_range
  ;

constant_part_select_range
  : constant_range
  | constant_indexed_range
  ;

constant_range: constant_expression COLON constant_expression;

constant_indexed_range
  : constant_expression part_select_op constant_expression
  ;

/*
 
 Non left-recursive grammar is slower by far
 
 expression : primary expression_prime
 |
 OPEN_PARENS expression CLOSE_PARENS expression_prime
 | (PLUS | MINUS | BANG | TILDA | BITW_AND |
 BITW_OR | BITW_XOR | REDUCTION_NAND | REDUCTION_NOR | REDUCTION_XNOR1| REDUCTION_XNOR2) (
 attribute_instance)* expression expression_prime
 | (PLUSPLUS | MINUSMINUS) attribute_instance*
 variable_lvalue expression_prime
 | variable_lvalue attribute_instance*
 (PLUSPLUS |
 MINUSMINUS)
 expression_prime
 | OPEN_PARENS variable_lvalue (ASSIGN_OP | ADD_ASSIGN
 | SUB_ASSIGN |
 MULT_ASSIGN| DIV_ASSIGN | MODULO_ASSIGN | BITW_AND_ASSIGN | BITW_OR_ASSIGN |
 BITW_XOR_ASSIGN |
 BITW_LEFT_SHIFT_ASSIGN | BITW_RIGHT_SHIFT_ASSIGN | ARITH_SHIFT_LEFT_ASSIGN |
 ARITH_SHIFT_RIGHT_ASSIGN) expression CLOSE_PARENS expression_prime
 | OPEN_PARENS expression
 MATCHES pattern (LOGICAL_AND expression)* CLOSE_PARENS QMARK attribute_instance* expression
 COLON
 expression expression_prime
 | TAGGED identifier expression? expression_prime ;
 
 expression_prime
 : STARSTAR attribute_instance* expression expression_prime
 | (STAR | DIV |
 PERCENT)
 attribute_instance* expression expression_prime
 | (PLUS | MINUS) (
 attribute_instance)*
 expression expression_prime
 | (SHIFT_RIGHT | SHIFT_LEFT |
 ARITH_SHIFT_RIGHT
 | ARITH_SHIFT_LEFT)
 attribute_instance* expression expression_prime
 | (
 LESS | LESS_EQUAL |
 GREATER | GREATER_EQUAL
 | INSIDE) attribute_instance* expression
 expression_prime
 | (EQUIV |
 NOTEQUAL |
 BINARY_WILDCARD_EQUAL | BINARY_WILDCARD_NOTEQUAL |
 FOUR_STATE_LOGIC_EQUAL |
 FOUR_STATE_LOGIC_NOTEQUAL | WILD_EQUAL_OP | WILD_NOTEQUAL_OP) (
 attribute_instance)* expression
 expression_prime
 | BITW_AND attribute_instance* expression
 expression_prime
 | (
 REDUCTION_XNOR1
 | REDUCTION_XNOR2 | REDUCTION_NAND | REDUCTION_NOR |
 BITW_XOR) (
 attribute_instance)* expression
 expression_prime
 | BITW_OR attribute_instance*
 expression
 expression_prime
 | LOGICAL_AND
 attribute_instance* expression expression_prime
 |
 LOGICAL_OR (
 attribute_instance)* expression
 expression_prime
 | (LOGICAL_AND expression)*
 QMARK (
 attribute_instance)* expression COLON
 expression expression_prime
 | (IMPLY |
 EQUIVALENCE) (
 attribute_instance)* expression
 expression_prime
 | MATCHES pattern (
 LOGICAL_AND
 expression)*
 QMARK attribute_instance*
 expression expression_prime
 | INSIDE
 OPEN_CURLY
 open_range_list
 CLOSE_CURLY expression_prime
 |
 ;
 */

expression
  : primary
  | OPEN_PARENS expression CLOSE_PARENS
  | (
    PLUS
    | MINUS
    | BANG
    | TILDA
    | BITW_AND
    | BITW_OR
    | BITW_XOR
    | REDUCTION_NAND
    | REDUCTION_NOR
    | REDUCTION_XNOR1
    | REDUCTION_XNOR2
  ) attribute_instance* expression
  | (PLUSPLUS | MINUSMINUS) attribute_instance* variable_lvalue
  | variable_lvalue attribute_instance* (PLUSPLUS | MINUSMINUS)
  | OPEN_PARENS variable_lvalue (
    ASSIGN_OP
    | ADD_ASSIGN
    | SUB_ASSIGN
    | MULT_ASSIGN
    | DIV_ASSIGN
    | MODULO_ASSIGN
    | BITW_AND_ASSIGN
    | BITW_OR_ASSIGN
    | BITW_XOR_ASSIGN
    | BITW_LEFT_SHIFT_ASSIGN
    | BITW_RIGHT_SHIFT_ASSIGN
    | ARITH_SHIFT_LEFT_ASSIGN
    | ARITH_SHIFT_RIGHT_ASSIGN
  ) expression CLOSE_PARENS
  | OPEN_PARENS expression MATCHES pattern (
    LOGICAL_AND expression
  )* CLOSE_PARENS QMARK attribute_instance* expression COLON expression
  | TAGGED identifier expression?
  | expression STARSTAR attribute_instance* expression
  | expression (STAR | DIV | PERCENT) attribute_instance* expression
  | expression (PLUS | MINUS) attribute_instance* expression
  | expression (
    SHIFT_RIGHT
    | SHIFT_LEFT
    | ARITH_SHIFT_RIGHT
    | ARITH_SHIFT_LEFT
  ) attribute_instance* expression
  | expression (
    LESS
    | LESS_EQUAL
    | GREATER
    | GREATER_EQUAL
    | INSIDE
  ) attribute_instance* expression
  | expression (
    EQUIV
    | NOTEQUAL
    | BINARY_WILDCARD_EQUAL
    | BINARY_WILDCARD_NOTEQUAL
    | FOUR_STATE_LOGIC_EQUAL
    | FOUR_STATE_LOGIC_NOTEQUAL
    | WILD_EQUAL_OP
    | WILD_NOTEQUAL_OP
  ) attribute_instance* expression
  | expression BITW_AND attribute_instance* expression
  | expression (
    REDUCTION_XNOR1
    | REDUCTION_XNOR2
    | REDUCTION_NAND
    | REDUCTION_NOR
    | BITW_XOR
  ) attribute_instance* expression
  | expression BITW_OR attribute_instance* expression
  | expression LOGICAL_AND attribute_instance* expression
  | expression LOGICAL_OR attribute_instance* expression
  | <assoc = right> expression (LOGICAL_AND expression)* QMARK attribute_instance* expression COLON
      expression
  | <assoc = right> expression (IMPLY | EQUIVALENCE) attribute_instance* expression
  | expression MATCHES pattern (LOGICAL_AND expression)* QMARK attribute_instance* expression COLON
      expression
  | expression INSIDE OPEN_CURLY open_range_list CLOSE_CURLY
  ;

value_range
  : expression
  | OPEN_BRACKET expression COLON expression CLOSE_BRACKET
  ;

mintypmax_expression
  : expression (COLON expression COLON expression)?
  ;

module_path_expression
  : module_path_primary
  | unary_module_path_operator attribute_instance* module_path_primary
  | module_path_expression binary_module_path_operator attribute_instance* module_path_expression
  | module_path_expression conditional_operator attribute_instance* module_path_expression COLON
      module_path_expression
  ;

module_path_mintypmax_expression
  : module_path_expression (
    COLON module_path_expression COLON module_path_expression
  )?
  ;

range_expression: expression | part_select_range;

part_select_range: constant_range | indexed_range;

part_select_op: INC_PART_SELECT_OP | DEC_PART_SELECT_OP;

part_select_op_colon
  : INC_PART_SELECT_OP
  | DEC_PART_SELECT_OP
  | COLON
  ;

indexed_range: expression part_select_op constant_expression;

constant_primary
  : primary_literal
  | (package_scope | class_scope)? identifier constant_select (
    OPEN_BRACKET constant_range_expression CLOSE_BRACKET
  )?
  | constant_concatenation (
    OPEN_BRACKET constant_range_expression CLOSE_BRACKET
  )?
  | constant_multiple_concatenation (
    OPEN_BRACKET constant_range_expression CLOSE_BRACKET
  )?
  | subroutine_call
  | constant_cast
  | constant_assignment_pattern_expression
  | type_reference
  | dollar_keyword
  | OPEN_PARENS constant_expression (
    COLON constant_expression COLON constant_expression
  )? CLOSE_PARENS
  ;

module_path_primary
  : number
  | identifier
  | module_path_concatenation
  | module_path_multiple_concatenation
  | subroutine_call
  | OPEN_PARENS module_path_mintypmax_expression CLOSE_PARENS
  ;

/*
 Replaces let_expression, tf_call, method_call
 */
complex_func_call
  : (
    implicit_class_handle DOT
    | class_scope
    | package_scope
    | dollar_keyword
    | LOCAL COLONCOLON
  )? dollar_root_keyword? identifier (
    (OPEN_BRACKET constant_expression CLOSE_BRACKET)* DOT identifier
  )* attribute_instance* (
    (OPEN_PARENS (list_of_arguments) CLOSE_PARENS)
    | select
  ) (DOT method_call_body)?
  ;

primary
  : primary_literal
  | complex_func_call
  | (concatenation | multiple_concatenation) (
    OPEN_BRACKET range_expression CLOSE_BRACKET
  )?
  //    | OPEN_PARENS mintypmax_expression CLOSE_PARENS
  | cast
  | assignment_pattern_expression
  | streaming_concatenation
  | system_task
  | class_type COLONCOLON method_call_body
  | this_keyword
  | dollar_keyword
  | null_keyword
  | empty_queue
  | randomize_call
  // mintypmax_expression moved here:
  | OPEN_PARENS expression COLON expression COLON expression CLOSE_PARENS
  ;

this_keyword: THIS;

super_keyword: SUPER;

dollar_keyword: DOLLAR;

dollar_root_keyword: DOLLAR_ROOT DOT;

this_dot_super: THIS DOT SUPER;

null_keyword: NULL_KEYWORD;

time_literal: Integral_number time_unit | Real_number time_unit;
//REMOVED | Unsigned_number time_unit | Fixed_point_number time_unit;

time_unit: Simple_identifier;

implicit_class_handle
  : this_keyword
  | super_keyword
  | this_dot_super
  ;

bit_select: (OPEN_BRACKET expression CLOSE_BRACKET)*;

select
  : ((DOT identifier bit_select)* DOT identifier)? bit_select (
    OPEN_BRACKET part_select_range CLOSE_BRACKET
  )?
  ;

nonrange_select
  : ((DOT identifier bit_select)* DOT identifier)? bit_select
  ;

constant_bit_select
  : (OPEN_BRACKET constant_expression CLOSE_BRACKET)*
  ;

constant_select
  : ((DOT identifier constant_bit_select)* DOT identifier)? constant_bit_select (
    OPEN_BRACKET constant_part_select_range CLOSE_BRACKET
  )?
  ;

primary_literal
  : number
  | time_literal
  | unbased_unsized_literal
  | string_value
  | identifier
  ;

constant_cast
  : casting_type TICK (
    OPEN_PARENS constant_expression CLOSE_PARENS
    | constant_concatenation
    | constant_multiple_concatenation
  )
  ;

cast
  : casting_type TICK (
    OPEN_PARENS expression CLOSE_PARENS
    | concatenation
    | multiple_concatenation
  )
  ;

net_lvalue
  : ps_or_hierarchical_identifier constant_select
  | OPEN_CURLY net_lvalue (COMMA net_lvalue)* CLOSE_CURLY
  | assignment_pattern_expression_type? assignment_pattern_net_lvalue
  ;

variable_lvalue
  : (implicit_class_handle DOT | package_scope)? ps_or_hierarchical_identifier select
  | OPEN_CURLY variable_lvalue (COMMA variable_lvalue)* CLOSE_CURLY
  | assignment_pattern_expression_type? assignment_pattern_variable_lvalue
  | streaming_concatenation
  ;

nonrange_variable_lvalue
  : (implicit_class_handle DOT | package_scope)? (
    identifier
    | hierarchical_identifier
  ) nonrange_select
  ;

inc_or_dec_operator: PLUSPLUS | MINUSMINUS;

unary_module_path_operator
  : BANG            # UnaryModOp_Not
  | TILDA           # UnaryModOp_Tilda
  | BITW_AND        # UnaryModOp_BitwAnd
  | REDUCTION_NAND  # UnaryModOp_ReductNand
  | BITW_OR         # UnaryModOp_BitwOr
  | REDUCTION_NOR   # UnaryModOp_ReductNor
  | BITW_XOR        # UnaryModOp_BitwXor
  | REDUCTION_XNOR1 # UnaryModOp_ReductXNor1
  | REDUCTION_XNOR2 # UnaryModOp_ReductXnor2
  ;

binary_module_path_operator
  : EQUIV           # BinModOp_Equiv
  | NOTEQUAL        # BinModOp_NotEqual
  | LOGICAL_AND     # BinModOp_LogicAnd
  | LOGICAL_OR      # BinModOp_LogicOr
  | BITW_AND        # BinModOp_BitwAnd
  | BITW_OR         # BinModOp_BitwOr
  | BITW_XOR        # BinModOp_BitwXor
  | REDUCTION_XNOR1 # BinModOp_ReductXnor1
  | REDUCTION_XNOR2 # BinModOp_ReductXnor2
  ;

number
  : Integral_number
  | Real_number
  | ONE_TICK_b0
  | ONE_TICK_b1
  | ONE_TICK_B0
  | ONE_TICK_B1
  | TICK_b0
  | TICK_b1
  | TICK_B0
  | TICK_B1
  | TICK_0
  | TICK_1
  | ONE_TICK_bx
  | ONE_TICK_bX
  | ONE_TICK_Bx
  | ONE_TICK_BX
  ;

unbased_unsized_literal: TICK Simple_identifier;

attribute_instance
  : OPEN_PARENS_STAR attr_spec (COMMA attr_spec)* STAR_CLOSE_PARENS
  ;

attr_spec: attr_name (ASSIGN_OP constant_expression)?;

attr_name: identifier;

hierarchical_identifier
  : dollar_root_keyword? identifier (
    (OPEN_BRACKET constant_expression CLOSE_BRACKET)* DOT identifier
  )+
  ;

identifier
  : Simple_identifier
  | Escaped_identifier
  | THIS // System Verilog keyword
  | RANDOMIZE // System Verilog keyword
  | SAMPLE
  ; // System Verilog keyword

interface_identifier
  : dollar_root_keyword? identifier (
    (OPEN_BRACKET constant_expression CLOSE_BRACKET)* DOT identifier
  )*
  ;

package_scope
  : (
    Simple_identifier
    | Escaped_identifier
    | THIS
    | RANDOMIZE
    | SAMPLE
    | DOLLAR_UNIT
  ) COLONCOLON
  ;

ps_identifier
  : (
    Simple_identifier
    | Escaped_identifier
    | THIS
    | RANDOMIZE
    | SAMPLE
    | DOLLAR_UNIT
  ) (
    COLONCOLON (
      Simple_identifier
      | Escaped_identifier
      | THIS
      | RANDOMIZE
      | SAMPLE
    )
  )?
  ;

ps_or_hierarchical_identifier
  : package_scope? identifier
  | hierarchical_identifier
  ;

ps_or_hierarchical_array_identifier
  : (implicit_class_handle DOT | class_scope | package_scope)? dollar_root_keyword? identifier (
    (OPEN_BRACKET constant_expression CLOSE_BRACKET)* DOT identifier
  )*
  ;

ps_or_hierarchical_sequence_identifier
  : ps_or_hierarchical_array_identifier
  ;

ps_type_identifier
  : (LOCAL COLONCOLON | package_scope)? identifier
  ;

system_task
  : system_task_names (
    OPEN_PARENS (
      list_of_arguments (COMMA clocking_event)?
      | data_type
    ) CLOSE_PARENS
  )?
  ;

system_task_names
  : DOLLAR Simple_identifier (DOLLAR Simple_identifier)*
  | DOLLAR TIME
  | DOLLAR REALTIME
  | DOLLAR SIGNED
  | DOLLAR UNSIGNED
  | DOLLAR ASSERT
  ;

top_directives
  : timescale_directive
  | uselib_directive
  | BACK_TICK Simple_identifier (
    number
    | Simple_identifier
    | Real_number
  )?
  | begin_keywords_directive
  | end_keywords_directive
  | unconnected_drive_directive
  | nounconnected_drive_directive
  | default_nettype_directive
  | default_decay_time_directive
  | default_trireg_strenght_directive
  | delay_mode_distributed_directive
  | delay_mode_path_directive
  | delay_mode_unit_directive
  | delay_mode_zero_directive
  | protect_directive
  | endprotect_directive
  | protected_directive
  | endprotected_directive
  | expand_vectornets_directive
  | noexpand_vectornets_directive
  | autoexpand_vectornets_directive
  | remove_gatename_directive
  | noremove_gatenames_directive
  | remove_netname_directive
  | noremove_netnames_directive
  | accelerate_directive
  | noaccelerate_directive
  | disable_portfaults_directive
  | enable_portfaults_directive
  | nosuppress_faults_directive
  | suppress_faults_directive
  | signed_directive
  | unsigned_directive
  | celldefine_directive
  | endcelldefine_directive
  | pragma_directive
  ;

pragma_directive
  : TICK_PRAGMA Simple_identifier (
    pragma_expression (COMMA pragma_expression)*
  )?
  ;

pragma_expression
  : Simple_identifier
  | Simple_identifier ASSIGN_OP pragma_value
  | pragma_value
  | BEGIN
  | END
  ;

pragma_value
  : OPEN_PARENS pragma_expression (COMMA pragma_expression)* CLOSE_PARENS
  | number
  | string_value
  | Simple_identifier
  ;

timescale_directive
  : TICK_TIMESCALE Integral_number Simple_identifier DIV Integral_number Simple_identifier
  ;

begin_keywords_directive: TICK_BEGIN_KEYWORDS String;

end_keywords_directive: TICK_END_KEYWORDS;

unconnected_drive_directive
  : TICK_UNCONNECTED_DRIVE (Simple_identifier | PULL0 | PULL1)
  ;

nounconnected_drive_directive: TICK_NOUNCONNECTED_DRIVE;

default_nettype_directive
  : TICK_DEFAULT_NETTYPE (Simple_identifier | net_type)
  ;

uselib_directive: TICK_USELIB;

celldefine_directive: TICK_CELLDEFINE;
endcelldefine_directive: TICK_ENDCELLDEFINE;
protect_directive: TICK_PROTECT;
endprotect_directive: TICK_ENDPROTECT;
protected_directive: TICK_PROTECTED;
endprotected_directive: TICK_ENDPROTECTED;
expand_vectornets_directive: TICK_EXPAND_VECTORNETS;
noexpand_vectornets_directive: TICK_NOEXPAND_VECTORNETS;
autoexpand_vectornets_directive: TICK_AUTOEXPAND_VECTORNETS;
disable_portfaults_directive: TICK_DISABLE_PORTFAULTS;
enable_portfaults_directive: TICK_ENABLE_PORTFAULTS;
nosuppress_faults_directive: TICK_NOSUPPRESS_FAULTS;
suppress_faults_directive: TICK_SUPPRESS_FAULTS;
signed_directive: TICK_SIGNED;
unsigned_directive: TICK_UNSIGNED;
remove_gatename_directive: TICK_REMOVE_GATENAME;
noremove_gatenames_directive: TICK_NOREMOVE_GATENAMES;
remove_netname_directive: TICK_REMOVE_NETNAME;
noremove_netnames_directive: TICK_NOREMOVE_NETNAMES;
accelerate_directive: TICK_ACCELERATE;
noaccelerate_directive: TICK_NOACCELERATE;
default_trireg_strenght_directive
  : TICK_DEFAULT_TRIREG_STRENGTH number
  ;
default_decay_time_directive
  : TICK_DEFAULT_DECAY_TIME (number | Simple_identifier)
  ;
delay_mode_distributed_directive: TICK_DELAY_MODE_DISTRIBUTED;
delay_mode_path_directive: TICK_DELAY_MODE_PATH;
delay_mode_unit_directive: TICK_DELAY_MODE_UNIT;
delay_mode_zero_directive: TICK_DELAY_MODE_ZERO;

surelog_macro_not_defined: SURELOG_MACRO_NOT_DEFINED;

slline: TICK_LINE Integral_number String Integral_number;

config_declaration
  : CONFIG identifier SEMICOLON (
    local_parameter_declaration SEMICOLON
  )* design_statement config_rule_statement* ENDCONFIG (
    COLON identifier
  )?
  ;

design_statement
  : DESIGN ((identifier DOT)? identifier)* SEMICOLON
  ;

config_rule_statement
  : default_clause liblist_clause SEMICOLON
  | inst_clause liblist_clause SEMICOLON
  | inst_clause use_clause_config SEMICOLON
  | inst_clause use_clause SEMICOLON
  | cell_clause liblist_clause SEMICOLON
  | cell_clause use_clause_config SEMICOLON
  | cell_clause use_clause SEMICOLON
  ;

default_clause: DEFAULT;

inst_clause: INSTANCE inst_name;

inst_name: identifier (DOT identifier)*;

cell_clause: CELL (identifier DOT)? identifier;

liblist_clause: LIBLIST identifier*;

use_clause_config
  : USE (identifier DOT)? identifier COLON CONFIG
  | USE named_parameter_assignment (
    COMMA named_parameter_assignment
  )* COLON CONFIG
  | USE (identifier DOT)? identifier named_parameter_assignment (
    COMMA named_parameter_assignment
  )* COLON CONFIG
  ;

use_clause
  : USE (identifier DOT)? identifier
  | USE named_parameter_assignment (
    COMMA named_parameter_assignment
  )*
  | USE (identifier DOT)? identifier named_parameter_assignment (
    COMMA named_parameter_assignment
  )*
  | USE parameter_value_assignment
  ;
