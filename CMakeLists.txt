include_directories( ./include )

set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -std=c++11")

set(SOURCES
  src/SpecSFS.cpp
  )

add_llvm_loadable_module(SpecSFS
    ${SOURCES}
  )

