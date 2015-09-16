cmake_minimum_required(VERSION 2.8)

function(list_prefix var prefix)

  set(listvar "")

  foreach(f ${ARGN})
    list(APPEND listvar "${prefix}/${f}")
  endforeach(f)

  set(${var} "${listvar}" PARENT_SCOPE)

endfunction(list_prefix)

function(add_cpplint_headers TARGET_NAME)

  set(lint_names "")
  list_prefix(lint_names ${PROJECT_SOURCE_DIR}/include ${ARGN})

  add_custom_command(TARGET ${TARGET_NAME} 
    PRE_LINK
    COMMAND "/home/ddevec/prefix/bin/cpplint.py" 
    ARGS    "--counting=detailed"
            "--extensions=cpp,h"
            "--linelength=80"
            "--filter=-readability/function"
            ${lint_names}
    COMMENT "Linting ${TARGET_NAME}"
    VERBATIM)

endfunction(add_cpplint_headers)

function(add_cpplint_target TARGET_NAME)

  set(lint_names "")
  list_prefix(lint_names ${CMAKE_CURRENT_SOURCE_DIR} ${ARGN})

  add_custom_command(TARGET ${TARGET_NAME} 
    PRE_LINK
    COMMAND "/home/ddevec/prefix/bin/cpplint.py" 
    ARGS    "--counting=detailed"
            "--extensions=cpp,h"
            "--linelength=80"
            "--filter=-readability/function"
            ${lint_names}
    COMMENT "Linting ${TARGET_NAME}"
    VERBATIM)

endfunction(add_cpplint_target)

include_directories( . ${PROJECT_SOURCE_DIR}/include )

find_package(LLVM REQUIRED CONFIG)

include(AddLLVM)

add_definitions(${LLVM_DEFINITOINS})
include_directories(${LLVM_INCLUDE_DIRS})
link_directories(${LLVM_LIBRARY_DIRS})

list(APPEND CMAKE_MODULE_PATH "${LLVM_CMAKE_DIR}")

#set(CMAKE_CXX_COMPILER "clang-3.6")
set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -std=c++11 -D__STDC_FORMAT_MACROS -D__STDC_LIMIT_MACROS -fPIC -fvisibility-inlines-hidden -fno-rtti -Wall -Wextra -pedantic -Wno-deprecated -Wwrite-strings -Wno-long-long -fno-exceptions")

set(SPECSFS_SOURCES
  src/SpecSFS.cpp

  src/Debug.cpp

  src/ObjectMap.cpp
  src/ControlFlowGraph.cpp

  src/Andersens.cpp

  src/IdentifyObjects.cpp
  src/Optimize.cpp
  src/ComputeSSA.cpp
  src/Partition.cpp
  src/Solve.cpp
  )

set(SPECSFS_HEADERS
  SpecSFS.h

  util.h
  SEG.h
  Debug.h

  SolveHelpers.h

  ObjectMap.h
  DUG.h

  Andersens.h
  )

add_llvm_loadable_module(SpecSFS
    ${SPECSFS_SOURCES}
  )

add_cpplint_target(SpecSFS ${SPECSFS_SOURCES})
add_cpplint_headers(SpecSFS ${SPECSFS_HEADERS})

add_subdirectory(test)
add_subdirectory(lib)

