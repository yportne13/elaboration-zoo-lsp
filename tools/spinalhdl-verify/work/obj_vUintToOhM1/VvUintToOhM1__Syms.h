// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Symbol table internal header
//
// Internal details; most calling programs do not need this header,
// unless using verilator public meta comments.

#ifndef _VVUINTTOOHM1__SYMS_H_
#define _VVUINTTOOHM1__SYMS_H_  // guard

#include "verilated.h"

// INCLUDE MODULE CLASSES
#include "VvUintToOhM1.h"

// SYMS CLASS
class VvUintToOhM1__Syms : public VerilatedSyms {
  public:
    
    // LOCAL STATE
    const char* __Vm_namep;
    bool __Vm_didInit;
    
    // SUBCELL STATE
    VvUintToOhM1*                  TOPp;
    
    // CREATORS
    VvUintToOhM1__Syms(VvUintToOhM1* topp, const char* namep);
    ~VvUintToOhM1__Syms() {}
    
    // METHODS
    inline const char* name() { return __Vm_namep; }
    
} VL_ATTR_ALIGNED(VL_CACHE_LINE_BYTES);

#endif  // guard
