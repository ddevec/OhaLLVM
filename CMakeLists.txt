cmake_minimum_required(VERSION 2.8)

function(list_prefix var prefix)

  set(listvar "")

  foreach(f ${ARGN})
    list(APPEND listvar "${prefix}/${f}")
  endforeach(f)

  set(${var} "${listvar}" PARENT_SCOPE)

endfunction(list_prefix)

function(add_lint_command TARGET_NAME)

#  foreach(fil ${ARGN})
#    add_custom_command(TARGET ${TARGET_NAME} 
#      COMMAND "/home/ddevec/prefix/bin/cpplint.py" 
#      ARGS    "--counting=detailed"
#              "--extensions=cpp,h"
#              "--linelength=80"
#              "--filter=-readability/function"
#              ${fil}
#      DEPENDS ${fil}
#      COMMENT "Linting ${TARGET_NAME}"
#      VERBATIM)
#  endforeach(fil)

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
endfunction(add_lint_command)

function(add_cpplint_headers TARGET_NAME)

  set(lint_names "")
  list_prefix(lint_names ${PROJECT_SOURCE_DIR}/include ${ARGN})

  add_lint_command(${TARGET_NAME} ${lint_names})

endfunction(add_cpplint_headers)

function(add_cpplint_target TARGET_NAME)

  set(lint_names "")
  list_prefix(lint_names ${CMAKE_CURRENT_SOURCE_DIR} ${ARGN})

  add_lint_command(${TARGET_NAME} ${lint_names})

endfunction(add_cpplint_target)

include_directories( . ${PROJECT_SOURCE_DIR}/include )

find_package(LLVM REQUIRED CONFIG)

include(AddLLVM)

add_definitions(${LLVM_DEFINITOINS})
include_directories(${LLVM_INCLUDE_DIRS})
link_directories(${LLVM_LIBRARY_DIRS})

list(APPEND CMAKE_MODULE_PATH "${LLVM_CMAKE_DIR}")

#FIXME... Shouldn't do this with full release
#set(CMAKE_CXX_FLAGS_RELWITHDEBINFO "-ggdb3 -O1")
#set(CMAKE_CXX_FLAGS_RELWITHDEBINFO "-g -O4 -DNDEBUG -DSPECSFS_NODEBUG")
set(CMAKE_CXX_FLAGS_RELWITHDEBINFO "-g -O4")
set(CMAKE_CXX_FLAGS_RELEASE "-O4 -DNDEBUG -DSPECSFS_NODEBUG")
#set(CMAKE_CXX_FLAGS_DEBUG "-O1 -g3")
set(CMAKE_CXX_FLAGS_DEBUG "-Og -g")

#set(CMAKE_CXX_COMPILER "g++-5")
#set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -std=c++14 -flto -D__STDC_FORMAT_MACROS -D__STDC_LIMIT_MACROS -fPIC -fvisibility-inlines-hidden -fno-rtti -Wall -Wextra -pedantic -Wno-deprecated -Wwrite-strings -Wno-long-long -fno-exceptions")
set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -std=c++11 -D__STDC_FORMAT_MACROS -D__STDC_LIMIT_MACROS -D__STDC_CONSTANT_MACROS -fPIC -fvisibility-inlines-hidden -fno-rtti -Wall -Wextra -pedantic -Wno-deprecated -Wwrite-strings -Wno-long-long -fno-exceptions")
set(CMAKE_EXE_LINKER_FLAGS "${CMAKE_EXE_LINKER_FLAGS} -std=c++11 -flto -D__STDC_FORMAT_MACROS -D__STDC_LIMIT_MACROS -fPIC -fvisibility-inlines-hidden -fno-rtti -Wall -Wextra -pedantic -Wno-deprecated -Wwrite-strings -Wno-long-long -fno-exceptions")
#set(CMAKE_CXX_LINKER_FLAGS "${CMAKE_CXX_LINKER_FLAGS} -flto")
#set(CMAKE_SHARED_LINKER_FLAGS "${CMAKE_SHARED_LINKER_FLAGS} -flto")

set(SPECSFS_SOURCES
  lib/UnusedFunctions/UnusedFunctions.cpp
  lib/PrintID.cpp

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

  src/DynPtstoOpt.cpp

  # Instrumentation passes
  lib/Instrument/IndirFcnTarget.cpp
  lib/Instrument/DynPtsto.cpp

  #uhh
  lib/TestAA.cpp
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

target_link_libraries(SpecSFS
  profiler
  )

add_cpplint_target(SpecSFS ${SPECSFS_SOURCES})
add_cpplint_headers(SpecSFS ${SPECSFS_HEADERS})

set(PROF_INDIR_SOURCES
  lib/Instrument/StaticLibs/IndirFcnTargetLib.cpp
  )

add_library(prof_indir STATIC
  ${PROF_INDIR_SOURCES}
  )
add_cpplint_target(prof_indir ${PROF_INDIR_SOURCES})

set(PROF_DYNPTSTO_SOURCES
  lib/Instrument/StaticLibs/DynPtstoLib.cpp
  )
  

add_library(prof_ptsto STATIC
  ${PROF_DYNPTSTO_SOURCES}
  )
add_cpplint_target(prof_ptsto ${PROF_DYNPTSTO_SOURCES})

add_subdirectory(test)
#add_subdirectory(unit_test)

