# Surelog Preprocessor Architecture

## Overview

Surelog's preprocessor is not a simple text-replacement engine, but rather a sophisticated **full ANTLR-based parser** with its own grammar, data structures, and persistent caching mechanism. This architecture enables accurate tracking of file locations, macro expansions, and includes throughout the preprocessing phase, information that is essential for later compilation stages.

## Preprocessing Strategy

The preprocessor performs the following transformations:
- **Include files are replaced by their contents**: When an `` `include`` directive is encountered, the entire file content is inserted in place of the directive
- **Macro definitions are carved out**: Macro definition directives are removed from the preprocessed output but replaced with **equivalent whitespace** to preserve line numbering
- **Whitespace preservation**: This approach results in potentially large amounts of whitespace and blank lines in macro-heavy files, but this is intentional—it greatly simplifies the mathematical reconstruction of file/line information, especially when macros and includes are used in complex nested (imbricated) fashion

This whitespace-preserving strategy ensures that line numbers in the preprocessed output maintain a direct correspondence with the original source, making it straightforward to map errors and debug information back to the correct locations even through multiple levels of macro expansion and file inclusion.

## Key Components

### 1. ANTLR Grammar and Parser

The preprocessor uses a dedicated ANTLR 4 grammar separate from the main SystemVerilog parser:

- **Grammar Files**:
  - [`grammar/SV3_1aPpParser.g4`](grammar/SV3_1aPpParser.g4) - Preprocessor parser grammar
  - [`grammar/SV3_1aPpLexer.g4`](grammar/SV3_1aPpLexer.g4) - Preprocessor lexer grammar

The parser grammar defines rules for all SystemVerilog preprocessor directives including:
- `ifdef_directive`, `ifndef_directive`, `else_directive`, `elsif_directive`, `endif_directive`
- `include_directive` 
- `macro_definition`, `macro_usage`
- `undef_directive`, `resetall_directive`
- `timescale_directive`, `line_directive`
- And many more preprocessor-specific constructs

### 2. IncludeFileInfo Data Structure

The [`IncludeFileInfo`](include/Surelog/SourceCompile/IncludeFileInfo.h) class is the core data structure for maintaining file and line tracking information:

```cpp
class IncludeFileInfo {
public:
  enum class Context : uint32_t { NONE = 0, INCLUDE = 1, MACRO = 2 };
  enum class Action : uint32_t { NONE = 0, PUSH = 1, POP = 2 };
  
  // Tracks:
  // - Context (include file or macro expansion)
  // - Section start line in preprocessed output
  // - Original file location (line, column)
  // - Push/Pop actions for nested contexts
  // - Opening/closing indices for paired directives
};
```

Key fields:
- `m_context`: Whether this is an `INCLUDE` file or `MACRO` expansion
- `m_sectionStartLine`: Line number in the preprocessed output
- `m_sectionFileId`/`m_sectionSymbolId`: References to the included file or macro
- `m_originalStartLine`/`m_originalStartColumn`: Original source location
- `m_action`: `PUSH` when entering a context, `POP` when exiting
- `m_indexOpening`/`m_indexClosing`: Paired indices for matching push/pop operations

### 3. SV3_1aPpTreeShapeListener

The [`SV3_1aPpTreeShapeListener`](src/SourceCompile/SV3_1aPpTreeShapeListener.cpp) class (derived from `SV3_1aPpTreeListenerHelper`) is the ANTLR tree listener that processes the parse tree and maintains the `IncludeFileInfo` records.

Key responsibilities:

#### Include File Processing
When processing `#include` directives ([lines 309-388](src/SourceCompile/SV3_1aPpTreeShapeListener.cpp#L309-L388)):
```cpp
// Records PUSH action when entering include file
openingIndex = m_pp->getSourceFile()->addIncludeFileInfo(
    IncludeFileInfo::Context::INCLUDE,
    1, // sectionStartLine
    symbolId, // include file symbol
    fileId,   // include file path
    // ... original location info
    IncludeFileInfo::Action::PUSH);

// Records POP action when exiting include file  
closingIndex = m_pp->getSourceFile()->addIncludeFileInfo(
    IncludeFileInfo::Context::INCLUDE,
    // ... location info
    IncludeFileInfo::Action::POP, 
    openingIndex, 0);
```

#### Macro Expansion Tracking
When processing macro expansions ([lines 503-594](src/SourceCompile/SV3_1aPpTreeShapeListener.cpp#L503-L594)):
```cpp
// Records PUSH when entering macro expansion
openingIndex = m_pp->getSourceFile()->addIncludeFileInfo(
    IncludeFileInfo::Context::MACRO,
    macroInf->m_startLine,
    BadSymbolId,
    macroInf->m_fileId,
    // ... location info
    IncludeFileInfo::Action::PUSH);

// Records POP when exiting macro expansion
closingIndex = m_pp->getSourceFile()->addIncludeFileInfo(
    IncludeFileInfo::Context::MACRO,
    // ... location info  
    IncludeFileInfo::Action::POP,
    openingIndex, 0);
```

#### Nested Context Tracking
The same `IncludeFileInfo` mechanism handles complex nested scenarios, including:
- **Macro expansions that contain `include directives**: When a macro body contains an `include statement, the preprocessor tracks both the macro expansion context (MACRO) and the subsequent file inclusion context (INCLUDE)
- **Include files that define and use macros**: Files brought in via `include can define macros that are then expanded, creating nested INCLUDE→MACRO contexts
- **Recursive macro expansions**: When macros expand to other macro invocations, multiple MACRO contexts are pushed and popped in sequence

This unified tracking system ensures that any combination of macro expansions and file includes maintains accurate source location information through arbitrary levels of nesting.

#### Debug Output
The `-d incl` command-line option outputs the entire `IncludeFileInfo` data structure to stderr for debugging purposes. This is implemented in [`PreprocessFile::reportIncludeInfo()`](src/SourceCompile/PreprocessFile.cpp#L659-L677) and called from [`CompileSourceFile`](src/SourceCompile/CompileSourceFile.cpp#L244-L245):

```cpp
if (m_commandLineParser->getDebugIncludeFileInfo())
    std::cerr << m_pp->reportIncludeInfo();
```

The debug output shows:
- Context type ("inc" for INCLUDE, "mac" for MACRO)
- Original source location (line,column:endLine,endColumn)
- Action ("in" for PUSH, "out" for POP)
- File paths and symbols involved
- Opening/closing index pairs

This provides a complete trace of all preprocessor context changes, invaluable for debugging complex preprocessing issues.

### 4. Cache Persistence Mechanism

The preprocessor output and associated `IncludeFileInfo` records are persisted to disk using Cap'n Proto serialization:

#### PPCache Class
[`PPCache`](src/Cache/PPCache.cpp) handles saving and restoring preprocessor state:

- **Saving** ([`PreprocessFile::saveCache()`](src/SourceCompile/PreprocessFile.cpp#L1289-L1306)):
  ```cpp
  void PreprocessFile::saveCache() {
    if (!m_usingCachedVersion) {
      PPCache cache(this);
      cache.save();
    }
  }
  ```

- **Restoring** ([lines 362-365](src/SourceCompile/PreprocessFile.cpp#L362-L365)):
  ```cpp
  PPCache cache(this);
  if (cache.restore(clp->lowMem() || clp->noCacheHash())) {
    m_usingCachedVersion = true;
  }
  ```

#### IncludeFileInfo Serialization
The [`cacheIncludeFileInfos()`](src/Cache/PPCache.cpp#L419-L438) method serializes the `IncludeFileInfo` vector:
```cpp
void PPCache::cacheIncludeFileInfos(::PPCache::Builder builder,
                                    SymbolTable& targetSymbols,
                                    const SymbolTable& sourceSymbols) {
  const std::vector<IncludeFileInfo>& sourceIncludeFileInfos = 
      m_pp->getIncludeFileInfo();
  
  // Serialize each IncludeFileInfo record
  for (const IncludeFileInfo& sourceIncludeFileInfo : sourceIncludeFileInfos) {
    // Copy symbol IDs and path IDs to cache
    // Store all context, action, and location information
  }
}
```

## Data Flow

1. **Parsing Phase**: ANTLR parses the input file using the preprocessor grammar
2. **Tree Walking**: `SV3_1aPpTreeShapeListener` walks the parse tree:
   - Processes each preprocessor directive
   - Creates `IncludeFileInfo` records for includes and macros
   - Maintains push/pop pairs for proper nesting
3. **Output Generation**: Preprocessed text is generated alongside the `IncludeFileInfo` records
4. **Caching**: Both the preprocessed text and `IncludeFileInfo` are serialized to the cache directory
5. **Parser Integration**: When the main parser processes the preprocessed file, it uses the `IncludeFileInfo` records to:
   - Map locations in preprocessed text back to original source files
   - Provide accurate error reporting with original file locations
   - Support debugging and source navigation

## Benefits of This Architecture

1. **Accurate Location Tracking**: Every token in the preprocessed output can be mapped back to its original source location
2. **Performance**: Caching preprocessed files avoids redundant preprocessing
3. **Error Reporting**: Error messages reference the original source files, not the preprocessed text
4. **Debugging Support**: Tools can navigate from preprocessed code back to original sources
5. **Incremental Compilation**: Cached preprocessor output enables faster incremental builds

## Integration with Main Parser

The main SystemVerilog parser ([`grammar/SV3_1aParser.g4`](grammar/SV3_1aParser.g4)) consumes the preprocessed output along with the `IncludeFileInfo` records. This allows it to:
- Report errors at original source locations
- Build accurate ASTs with proper file/line information
- Support IDE features like "go to definition" across include boundaries

## Command Line Options

The preprocessor behavior can be controlled through various command-line options:

### Include Paths and Defines
- **`+incdir+<dir>`**: Add include search paths for `include directives
- **`+define+<name>=<value>`**: Define preprocessor macros from command line
- **`-D <name>=<value>`**: Alternative syntax for defining macros

### Preprocessor Output
- **`-writepp`**: Write preprocessed output files to `slpp_all/` or `slpp_unit/` directory
- **`-writeppfile <file>`**: Write preprocessed output to a specific file
- **`-lineoffsetascomments`**: Add line offset information as comments in preprocessed output

### Caching Control
- **`-nocache`**: Disable reading cached preprocessor output (forces re-preprocessing)
- **`-createcache`**: Create cache for precompiled packages
- **`-cachedir <dir>`**: Specify cache directory location

### Filtering Options
- **`-filterprotectedregions`**: Filter out synthesis pragma protected regions
- **`-filtercomments`**: Remove comments from preprocessed output
- **`-filterdirectives`**: Filter out simple preprocessor directives

### Debug Options
- **`-d incl`**: Output `IncludeFileInfo` debug trace to stderr
- **`-verbose`**: Provide verbose preprocessing information
- **`-profile`**: Generate profiling information for preprocessing

### Special Modes
- **`-fileunit`**: Compile each file as independent unit (affects preprocessing scope)
- **`-nobuiltin`**: Skip preprocessing of builtin SystemVerilog classes
- **`-parseonly`**: Only parse, reload preprocessor saved database

## Example Usage

When preprocessing a file with includes and macros:
```verilog
// main.sv
`include "defines.svh"
module top;
  `MY_MACRO(arg1, arg2)
endmodule
```

The preprocessor generates:
1. Preprocessed text with expanded includes and macros
2. `IncludeFileInfo` records tracking:
   - PUSH when entering "defines.svh"
   - POP when exiting "defines.svh"
   - PUSH when expanding MY_MACRO
   - POP when macro expansion completes

This information is cached and used by subsequent compilation stages to maintain accurate source tracking throughout the compilation pipeline.