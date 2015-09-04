
function(create_dis TARGET_NAME)

  add_custom_command(TARGET ${TARGET_NAME} POST_BUILD
    COMMAND   "llvm-dis"
    ARGS      "${TARGET_NAME}.bc"
    COMMENT   "Disassembling ${TARGET_NAME}"
    VERBATIM)

endfunction(create_dis)

function(create_test TARGET_NAME)
  add_executable(${TARGET_NAME} ${ARGN})

  create_dis(${TARGET_NAME})
endfunction(create_test)


set(CMAKE_C_COMPILER "clang")
#-Wno-format-security gets rid of some warnings due to the fakeness of my tests
set(CMAKE_C_FLAGS "-Wno-format-security -O0 -emit-llvm")
set(CMAKE_C_LINK_EXECUTABLE "llvm-ld -disable-opt <LINK_FLAGS> <OBJECTS> -o <TARGET>")

create_test(simple_fcn
    simple_fcn.c
  )

create_test(simple_fcn2
    simple_fcn2.c
  )

create_test(simple_indr_fcn
    simple_indr_fcn.c
  )

create_test(simple_indr_loop
    simple_indr_loop.c
  )

create_test(test_strong_update
    test_strong_update.c
  )

create_test(test_struct
    test_struct.c
  )

