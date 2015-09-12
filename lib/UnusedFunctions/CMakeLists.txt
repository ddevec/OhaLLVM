set(PROJECT_NAME UnusedFunctions)

set(SOURCES
  UnusedFunctions.cpp
  )

set(HEADERS
  lib/UnusedFunctions.h
  )

add_llvm_loadable_module(${PROJECT_NAME}
    ${SOURCES}
  )

add_cpplint_target(${PROJECT_NAME} ${SOURCES})
add_cpplint_headers(${PROJECT_NAME} ${HEADERS})
