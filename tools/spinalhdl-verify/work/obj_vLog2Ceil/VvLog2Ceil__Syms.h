// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Symbol table internal header
//
// Internal details; most calling programs do not need this header,
// unless using verilator public meta comments.

#ifndef _VVLOG2CEIL__SYMS_H_
#define _VVLOG2CEIL__SYMS_H_  // guard

#include "verilated.h"

// INCLUDE MODULE CLASSES
#include "VvLog2Ceil.h"

// SYMS CLASS
class VvLog2Ceil__Syms : public VerilatedSyms {
  public:
    
    // LOCAL STATE
    const char* __Vm_namep;
    bool __Vm_didInit;
    
    // SUBCELL STATE
    VvLog2Ceil*                    TOPp;
    
    // CREATORS
    VvLog2Ceil__Syms(VvLog2Ceil* topp, const char* namep);
    ~VvLog2Ceil__Syms() {}
    
    // METHODS
    inline const char* name() { return __Vm_namep; }
    
} VL_ATTR_ALIGNED(VL_CACHE_LINE_BYTES);

#endif  // guard
