// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Primary design header
//
// This header should be included by all source files instantiating the design.
// The class here is then constructed to instantiate the design.
// See the Verilator manual for examples.

#ifndef _VVDELAYEVENT_H_
#define _VVDELAYEVENT_H_  // guard

#include "verilated.h"

//==========

class VvDelayEvent__Syms;

//----------

VL_MODULE(VvDelayEvent) {
  public:
    
    // PORTS
    // The application code writes and reads these signals to
    // propagate new values into/out from the Verilated model.
    VL_IN8(clk,0,0);
    VL_IN8(reset,0,0);
    VL_IN8(ev,0,0);
    VL_OUT8(de,0,0);
    
    // LOCAL SIGNALS
    // Internals; generally not touched by application code
    CData/*0:0*/ vDelayEvent__DOT__d_run;
    CData/*1:0*/ vDelayEvent__DOT__d_cnt;
    
    // LOCAL VARIABLES
    // Internals; generally not touched by application code
    CData/*0:0*/ __Vclklast__TOP__clk;
    CData/*0:0*/ __Vclklast__TOP__reset;
    CData/*1:0*/ __Vtablechg1[16];
    static CData/*0:0*/ __Vtable1_vDelayEvent__DOT__d_run[16];
    static CData/*1:0*/ __Vtable1_vDelayEvent__DOT__d_cnt[16];
    
    // INTERNAL VARIABLES
    // Internals; generally not touched by application code
    VvDelayEvent__Syms* __VlSymsp;  // Symbol table
    
    // CONSTRUCTORS
  private:
    VL_UNCOPYABLE(VvDelayEvent);  ///< Copying not allowed
  public:
    /// Construct the model; called by application code
    /// The special name  may be used to make a wrapper with a
    /// single model invisible with respect to DPI scope names.
    VvDelayEvent(const char* name = "TOP");
    /// Destroy the model; called (often implicitly) by application code
    ~VvDelayEvent();
    
    // API METHODS
    /// Evaluate the model.  Application must call when inputs change.
    void eval() { eval_step(); }
    /// Evaluate when calling multiple units/models per time step.
    void eval_step();
    /// Evaluate at end of a timestep for tracing, when using eval_step().
    /// Application must call after all eval() and before time changes.
    void eval_end_step() {}
    /// Simulation complete, run final blocks.  Application must call on completion.
    void final();
    
    // INTERNAL METHODS
  private:
    static void _eval_initial_loop(VvDelayEvent__Syms* __restrict vlSymsp);
  public:
    void __Vconfigure(VvDelayEvent__Syms* symsp, bool first);
  private:
    static QData _change_request(VvDelayEvent__Syms* __restrict vlSymsp);
    static QData _change_request_1(VvDelayEvent__Syms* __restrict vlSymsp);
    void _ctor_var_reset() VL_ATTR_COLD;
  public:
    static void _eval(VvDelayEvent__Syms* __restrict vlSymsp);
  private:
#ifdef VL_DEBUG
    void _eval_debug_assertions();
#endif  // VL_DEBUG
  public:
    static void _eval_initial(VvDelayEvent__Syms* __restrict vlSymsp) VL_ATTR_COLD;
    static void _eval_settle(VvDelayEvent__Syms* __restrict vlSymsp) VL_ATTR_COLD;
    static void _sequent__TOP__1(VvDelayEvent__Syms* __restrict vlSymsp);
    static void _settle__TOP__2(VvDelayEvent__Syms* __restrict vlSymsp) VL_ATTR_COLD;
} VL_ATTR_ALIGNED(VL_CACHE_LINE_BYTES);

//----------


#endif  // guard
