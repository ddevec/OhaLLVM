#function(create_dis TARGET_NAME)
  #add_custom_command(TARGET ${TARGET_NAME} POST_BUILD
    #COMMAND   "llvm-dis"
    #ARGS      "${TARGET_NAME}.bc"
    #COMMENT   "Disassembling ${TARGET_NAME}"
    #VERBATIM)
#endfunction(create_dis)

function(create_dis TARGET_NAME)
  # message("Creating DIS: ${TARGET_NAME} : ${ARGN}")
  add_custom_command(OUTPUT ${TARGET_NAME} POST_BUILD
    COMMAND "clang-3.1" -S -Wno-format-security -O0 -g -emit-llvm ${ARGN} -o ${TARGET_NAME}
    DEPENDS ${ARGN}
    COMMENT  "Disassembling ${TARGET_NAME}"
    VERBATIM)
endfunction(create_dis)

function(create_bc TARGET_NAME)
  # message("Creating bc: ${TARGET_NAME} : ${ARGN}")
  add_custom_command(OUTPUT ${TARGET_NAME} POST_BUILD
    COMMAND "llvm-as" -o=${TARGET_NAME} ${ARGN}
    DEPENDS ${ARGN}
    VERBATIM)
endfunction(create_bc)

function(create_opt_with_dis OPT_FLAG OPT_SUFFIX opt_output)

  set(output_files "")

  foreach(f ${ARGN})
    set(f_nosuffix "")
    strip_suffix(f_nosuffix ".bc" ${f})
    set(output_var "${f_nosuffix}.${OPT_SUFFIX}.bc")


    add_custom_command(OUTPUT ${output_var} POST_BUILD
      COMMAND "opt" -${OPT_FLAG} ${f} > ${output_var}
      COMMAND "llvm-dis" ${output_var}
      DEPENDS ${f}
      VERBATIM)


    list(APPEND output_files ${output_var})
  endforeach(f)

  set(${opt_output} "${output_files}" PARENT_SCOPE)

endfunction(create_opt_with_dis)


function(create_opt OPT_FLAG OPT_SUFFIX opt_output)

  set(output_files "")

  foreach(f ${ARGN})
    set(f_nosuffix "")
    strip_suffix(f_nosuffix ".bc" ${f})
    set(output_var "${f_nosuffix}.${OPT_SUFFIX}.bc")


    add_custom_command(OUTPUT ${output_var} POST_BUILD
      COMMAND "opt" -${OPT_FLAG} ${f} > ${output_var}
      DEPENDS ${f}
      VERBATIM)

    list(APPEND output_files ${output_var})
  endforeach(f)

  set(${opt_output} "${output_files}" PARENT_SCOPE)

endfunction(create_opt)

function(llvm_compile TARGET_NAME OPTS)

  add_custom_target(${TARGET_NAME} ALL
    COMMAND "clang-3.1" ${OPTS} -g -O0 -o ${TARGET_NAME} ${ARGN}
    DEPENDS ${ARGN})

endfunction(llvm_compile)

function(append_suffix var appstr)
  set(listvar "")

  foreach(f ${ARGN})
    list(APPEND listvar "${f}${appstr}")
  endforeach(f)

  set(${var} "${listvar}" PARENT_SCOPE)
endfunction(append_suffix)

function(strip_suffix var suffix)
  set(listvar "")

  foreach(f ${ARGN})
    STRING(REGEX REPLACE "${suffix}$" "" VAR_WITHOUT_SUFFIX ${f})

    list(APPEND listvar "${VAR_WITHOUT_SUFFIX}")
  endforeach(f)

  set(${var} "${listvar}" PARENT_SCOPE)
endfunction(strip_suffix)

function(create_test TARGET_NAME)
  set(bc_list "")
  foreach(arg ${ARGN})
    set(base_name "")
    set(asm_name "")
    set(bc_name "")
    set(source_file "${CMAKE_CURRENT_SOURCE_DIR}/${arg}")

    strip_suffix(base_name ".c" ${arg})
    append_suffix(asm_name ".ll" ${base_name})
    append_suffix(bc_name ".bc" ${base_name})
    # message("have arg: " ${arg})
    # message("have source_file: " ${source_file})
    # message("have base_name: " ${base_name})
    # message("have asm_name: " ${asm_name})
    # message("have bc_name: " ${bc_name})

    # Convert the .c file to assembly
    create_dis(${asm_name} ${source_file})

    # Compile the assembly to bc
    create_bc(${bc_name} ${asm_name})

    list(APPEND bc_list ${bc_name})
  endforeach(arg)

  llvm_compile(${TARGET_NAME} "" ${bc_list})
endfunction(create_test)

function(create_opt_test TARGET_NAME)
  set(bc_list "")
  foreach(arg ${ARGN})
    set(base_name "")
    set(bc_name "")
    set(opt_name "")

    strip_suffix(base_name ".c" ${arg})
    append_suffix(bc_name ".bc" ${base_name})

    list(APPEND bc_list ${bc_name})
  endforeach(arg)

  set(edge_prof_list "")

  create_opt_with_dis("O3" "O3" edge_prof_list ${bc_list})

  set(prof_name "")
  append_suffix(prof_name ".O3" ${TARGET_NAME})


  llvm_compile(${prof_name} "" ${edge_prof_list})

endfunction(create_opt_test)


function(create_edge_profile TARGET_NAME)
  set(bc_list "")
  foreach(arg ${ARGN})
    set(base_name "")
    set(bc_name "")

    strip_suffix(base_name ".c" ${arg})
    append_suffix(bc_name ".bc" ${base_name})

    list(APPEND bc_list ${bc_name})
  endforeach(arg)

  set(edge_prof_list "")

  create_opt("insert-edge-profiling" "edge" edge_prof_list ${bc_list})

  set(prof_name "")
  append_suffix(prof_name ".edge" ${TARGET_NAME})

  llvm_compile(${prof_name} "-lprofile_rt" ${edge_prof_list})

endfunction(create_edge_profile)

function(create_path_profile TARGET_NAME)
  set(bc_list "")
  foreach(arg ${ARGN})
    set(base_name "")
    set(bc_name "")

    strip_suffix(base_name ".c" ${arg})
    append_suffix(bc_name ".bc" ${base_name})

    list(APPEND bc_list ${bc_name})
  endforeach(arg)

  set(path_prof_list "")

  create_opt("insert-path-profiling" "path" path_prof_list ${bc_list})

  set(prof_name "")
  append_suffix(prof_name ".path" ${TARGET_NAME})

  llvm_compile(${prof_name} "-lprofile_rt" ${path_prof_list})

endfunction(create_path_profile)

create_test(simple_fcn
    simple_fcn.c
  )

create_test(simple_fcn2
    simple_fcn2.c
  )

create_test(simple_call
    simple_call.c
  )

create_test(simple_indr_fcn
    simple_indr_fcn.c
  )

create_test(alloc_indir_fcn
    alloc_indir_fcn.c
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

create_test(test_memcpy
    test_memcpy.c
  )

create_test(simple_universal_value
    simple_universal_value.c
  )

create_test(test_echo_break
    test_echo_break.c
  )

create_test(glbl_const_init
    glbl_const_init.c
  )
create_opt_test(glbl_const_init
    glbl_const_init.c
  )

create_test(test_argv
    test_argv.c
  )

create_test(multi_malloc
    multi_malloc.c
  )

create_test(indir_two_malloc
    indir_two_malloc.c
  )

create_test(test_recursion
    test_recursion.c
  )

create_test(indir_recursion
    indir_recursion.c
  )

create_test(test_struct_store
    test_struct_store.c
  )

create_test(test_int_struct
    test_int_struct.c
  )

add_subdirectory(dce)

