// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Symbol table internal header
//
// Internal details; most calling programs do not need this header,
// unless using verilator public meta comments.

#ifndef _VVENDIANSWAP__SYMS_H_
#define _VVENDIANSWAP__SYMS_H_  // guard

#include "verilated.h"

// INCLUDE MODULE CLASSES
#include "VvEndianSwap.h"

// SYMS CLASS
class VvEndianSwap__Syms : public VerilatedSyms {
  public:
    
    // LOCAL STATE
    const char* __Vm_namep;
    bool __Vm_didInit;
    
    // SUBCELL STATE
    VvEndianSwap*                  TOPp;
    
    // CREATORS
    VvEndianSwap__Syms(VvEndianSwap* topp, const char* namep);
    ~VvEndianSwap__Syms() {}
    
    // METHODS
    inline const char* name() { return __Vm_namep; }
    
} VL_ATTR_ALIGNED(VL_CACHE_LINE_BYTES);

#endif  // guard
