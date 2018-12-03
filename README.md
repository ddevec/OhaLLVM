# OhaLLVM
This is the public release of our LLVM 
[Optimistc Hybrid Analysis](https://dl.acm.org/citation.cfm?id=3177153)
for C programs.  These tools were used to create and evaluate OptSlice
in "Optimistic Hybrid Analysis: Accelerating Dynamic Analysis through Predicated Static Analysis".

The OhaLLVM repository contains a set of LLVM analysis 
tools including a context sensitive and context insensitive 
version of Andersen's Points-to analysis, and a backward 
static slicer.  These tools were written for LLVM 3.1.

The repository can run these analyses in either traditional 
mode, or including dynamic run-time information to create a 
predicated static analysis.

Please see the [wiki](https://github.com/ddevec/OhaLLVM/wiki)
for setup and usage instructions.
