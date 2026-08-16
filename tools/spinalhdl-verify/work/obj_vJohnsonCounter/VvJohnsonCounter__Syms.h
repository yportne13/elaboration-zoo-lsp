// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Symbol table internal header
//
// Internal details; most calling programs do not need this header,
// unless using verilator public meta comments.

#ifndef _VVJOHNSONCOUNTER__SYMS_H_
#define _VVJOHNSONCOUNTER__SYMS_H_  // guard

#include "verilated.h"

// INCLUDE MODULE CLASSES
#include "VvJohnsonCounter.h"

// SYMS CLASS
class VvJohnsonCounter__Syms : public VerilatedSyms {
  public:
    
    // LOCAL STATE
    const char* __Vm_namep;
    bool __Vm_didInit;
    
    // SUBCELL STATE
    VvJohnsonCounter*              TOPp;
    
    // CREATORS
    VvJohnsonCounter__Syms(VvJohnsonCounter* topp, const char* namep);
    ~VvJohnsonCounter__Syms() {}
    
    // METHODS
    inline const char* name() { return __Vm_namep; }
    
} VL_ATTR_ALIGNED(VL_CACHE_LINE_BYTES);

#endif  // guard
