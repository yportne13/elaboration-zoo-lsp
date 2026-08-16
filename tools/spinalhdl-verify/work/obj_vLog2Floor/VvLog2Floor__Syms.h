// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Symbol table internal header
//
// Internal details; most calling programs do not need this header,
// unless using verilator public meta comments.

#ifndef _VVLOG2FLOOR__SYMS_H_
#define _VVLOG2FLOOR__SYMS_H_  // guard

#include "verilated.h"

// INCLUDE MODULE CLASSES
#include "VvLog2Floor.h"

// SYMS CLASS
class VvLog2Floor__Syms : public VerilatedSyms {
  public:
    
    // LOCAL STATE
    const char* __Vm_namep;
    bool __Vm_didInit;
    
    // SUBCELL STATE
    VvLog2Floor*                   TOPp;
    
    // CREATORS
    VvLog2Floor__Syms(VvLog2Floor* topp, const char* namep);
    ~VvLog2Floor__Syms() {}
    
    // METHODS
    inline const char* name() { return __Vm_namep; }
    
} VL_ATTR_ALIGNED(VL_CACHE_LINE_BYTES);

#endif  // guard
