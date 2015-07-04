cmake_minimum_required(VERSION 2.8)

function(list_prefix var prefix)

  set(list_var "")

  foreach(f ${ARGN})
    list(APPEND listvar "${prefix}/${f}")
  endforeach(f)

  set(${var} "${listvar}" PARENT_SCOPE)

endfunction(list_prefix)

function(add_cpplint_target TARGET_NAME)

  set(lint_names "")
  list_prefix(lint_names ${CMAKE_CURRENT_SOURCE_DIR} ${ARGN})

  add_custom_command(TARGET ${TARGET_NAME} 
    PRE_BUILD
    COMMAND "/home/ddevec/prefix/bin/cpplint.py" 
    ARGS    "--counting=detailed"
            "--extensions=cpp,h"
            "--linelength=80"
            "--filter=-readability/function"
            ${lint_names}
    COMMENT "Linting ${TARGET_NAME}"
    VERBATIM)

endfunction(add_cpplint_target)


include_directories( . )

find_package(LLVM REQUIRED CONFIG)

add_definitions(${LLVM_DEFINITOINS})
include_directories(${LLVM_INCLUDE_DIRS})

list(APPEND CMAKE_MODULE_PATH "${LLVM_CMAKE_DIR}")

include(AddLLVM)

set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -std=c++11")

set(SOURCES
  src/SpecSFS.cpp
  src/ObjectMap.cpp
  src/DUG.cpp
  src/IdentifyObjects.cpp
  src/Optimize.cpp
  )

set(HEADERS
  include/SpecSFS.h
  include/ObjectMap.h
  include/DUG.h
  )

add_llvm_loadable_module(SpecSFS
    ${SOURCES}
  )

add_cpplint_target(SpecSFS ${SOURCES})
add_cpplint_target(SpecSFS ${HEADERS})

add_subdirectory(test)

