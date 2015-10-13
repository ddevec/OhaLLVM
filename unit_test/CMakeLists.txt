enable_testing()

#Force our units to compile in testing mode
set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -DSPECSFS_IS_TEST")

add_subdirectory(seg)
add_subdirectory(ssa)

