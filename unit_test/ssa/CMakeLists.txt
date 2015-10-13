
add_executable(TestCreateGp
   ../../src/ComputeSSA.cpp
   TestCreateGp.cpp
   )

add_executable(TestT4
   ../../src/ComputeSSA.cpp
   TestT4.cpp
   )

add_executable(TestT2
   ../../src/ComputeSSA.cpp
   TestT2.cpp
   )

add_executable(TestT2_2
   ../../src/ComputeSSA.cpp
   TestT2_2.cpp
   )

add_executable(TestT6
   ../../src/ComputeSSA.cpp
   TestT6.cpp
   )

add_executable(TestT5
   ../../src/ComputeSSA.cpp
   TestT5.cpp
   )

add_test(SSATest TestCreateGp TestT4 TestT2 TestT2_2 TestT6 Test5)

