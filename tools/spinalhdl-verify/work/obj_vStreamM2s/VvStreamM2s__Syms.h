// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Symbol table internal header
//
// Internal details; most calling programs do not need this header,
// unless using verilator public meta comments.

#ifndef _VVSTREAMM2S__SYMS_H_
#define _VVSTREAMM2S__SYMS_H_  // guard

#include "verilated.h"

// INCLUDE MODULE CLASSES
#include "VvStreamM2s.h"

// SYMS CLASS
class VvStreamM2s__Syms : public VerilatedSyms {
  public:
    
    // LOCAL STATE
    const char* __Vm_namep;
    bool __Vm_didInit;
    
    // SUBCELL STATE
    VvStreamM2s*                   TOPp;
    
    // CREATORS
    VvStreamM2s__Syms(VvStreamM2s* topp, const char* namep);
    ~VvStreamM2s__Syms() {}
    
    // METHODS
    inline const char* name() { return __Vm_namep; }
    
} VL_ATTR_ALIGNED(VL_CACHE_LINE_BYTES);

#endif  // guard
