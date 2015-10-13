
add_executable(SCCTest1
   SCCTest1.cpp
   )

add_executable(SCCTest2
   SCCTest2.cpp
   )

add_test(SCCTest SCCTest1 SCCTest2)

