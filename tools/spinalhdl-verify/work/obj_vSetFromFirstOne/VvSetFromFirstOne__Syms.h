// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Symbol table internal header
//
// Internal details; most calling programs do not need this header,
// unless using verilator public meta comments.

#ifndef _VVSETFROMFIRSTONE__SYMS_H_
#define _VVSETFROMFIRSTONE__SYMS_H_  // guard

#include "verilated.h"

// INCLUDE MODULE CLASSES
#include "VvSetFromFirstOne.h"

// SYMS CLASS
class VvSetFromFirstOne__Syms : public VerilatedSyms {
  public:
    
    // LOCAL STATE
    const char* __Vm_namep;
    bool __Vm_didInit;
    
    // SUBCELL STATE
    VvSetFromFirstOne*             TOPp;
    
    // CREATORS
    VvSetFromFirstOne__Syms(VvSetFromFirstOne* topp, const char* namep);
    ~VvSetFromFirstOne__Syms() {}
    
    // METHODS
    inline const char* name() { return __Vm_namep; }
    
} VL_ATTR_ALIGNED(VL_CACHE_LINE_BYTES);

#endif  // guard
