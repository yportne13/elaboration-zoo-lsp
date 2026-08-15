// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Symbol table internal header
//
// Internal details; most calling programs do not need this header,
// unless using verilator public meta comments.

#ifndef _VVSTREAMMUX__SYMS_H_
#define _VVSTREAMMUX__SYMS_H_  // guard

#include "verilated.h"

// INCLUDE MODULE CLASSES
#include "VvStreamMux.h"

// SYMS CLASS
class VvStreamMux__Syms : public VerilatedSyms {
  public:
    
    // LOCAL STATE
    const char* __Vm_namep;
    bool __Vm_didInit;
    
    // SUBCELL STATE
    VvStreamMux*                   TOPp;
    
    // CREATORS
    VvStreamMux__Syms(VvStreamMux* topp, const char* namep);
    ~VvStreamMux__Syms() {}
    
    // METHODS
    inline const char* name() { return __Vm_namep; }
    
} VL_ATTR_ALIGNED(VL_CACHE_LINE_BYTES);

#endif  // guard
