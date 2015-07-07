
function(create_dis TARGET_NAME)

  add_custom_command(TARGET ${TARGET_NAME} POST_BUILD
    COMMAND   "llvm-dis"
    ARGS      "${TARGET_NAME}.bc"
    COMMENT   "Disassembling ${TARGET_NAME}"
    VERBATIM)

endfunction(create_dis)


set(CMAKE_C_COMPILER "clang")
#-Wno-format-security gets rid of some warnings due to the fakeness of my tests
set(CMAKE_C_FLAGS "-Wno-format-security -O0 -emit-llvm")
set(CMAKE_C_LINK_EXECUTABLE "llvm-ld -disable-opt <LINK_FLAGS> <OBJECTS> -o <TARGET>")


add_executable(simple_fcn
  simple_fcn.c)

add_executable(simple_fcn2
  simple_fcn2.c)

add_executable(simple_indr_fcn
  simple_indr_fcn.c)

create_dis(simple_fcn)
create_dis(simple_indr_fcn)
create_dis(simple_fcn2)

