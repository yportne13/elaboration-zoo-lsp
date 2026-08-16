// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Primary design header
//
// This header should be included by all source files instantiating the design.
// The class here is then constructed to instantiate the design.
// See the Verilator manual for examples.

#ifndef _VVPRESCALER_H_
#define _VVPRESCALER_H_  // guard

#include "verilated.h"

//==========

class VvPrescaler__Syms;

//----------

VL_MODULE(VvPrescaler) {
  public:
    
    // PORTS
    // The application code writes and reads these signals to
    // propagate new values into/out from the Verilated model.
    VL_IN8(clk,0,0);
    VL_IN8(reset,0,0);
    VL_IN8(lim,7,0);
    VL_OUT8(ov,0,0);
    
    // LOCAL SIGNALS
    // Internals; generally not touched by application code
    CData/*7:0*/ vPrescaler__DOT__p_cnt;
    
    // LOCAL VARIABLES
    // Internals; generally not touched by application code
    CData/*0:0*/ __Vclklast__TOP__clk;
    CData/*0:0*/ __Vclklast__TOP__reset;
    
    // INTERNAL VARIABLES
    // Internals; generally not touched by application code
    VvPrescaler__Syms* __VlSymsp;  // Symbol table
    
    // CONSTRUCTORS
  private:
    VL_UNCOPYABLE(VvPrescaler);  ///< Copying not allowed
  public:
    /// Construct the model; called by application code
    /// The special name  may be used to make a wrapper with a
    /// single model invisible with respect to DPI scope names.
    VvPrescaler(const char* name = "TOP");
    /// Destroy the model; called (often implicitly) by application code
    ~VvPrescaler();
    
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
    static void _eval_initial_loop(VvPrescaler__Syms* __restrict vlSymsp);
  public:
    void __Vconfigure(VvPrescaler__Syms* symsp, bool first);
  private:
    static QData _change_request(VvPrescaler__Syms* __restrict vlSymsp);
    static QData _change_request_1(VvPrescaler__Syms* __restrict vlSymsp);
    void _ctor_var_reset() VL_ATTR_COLD;
  public:
    static void _eval(VvPrescaler__Syms* __restrict vlSymsp);
  private:
#ifdef VL_DEBUG
    void _eval_debug_assertions();
#endif  // VL_DEBUG
  public:
    static void _eval_initial(VvPrescaler__Syms* __restrict vlSymsp) VL_ATTR_COLD;
    static void _eval_settle(VvPrescaler__Syms* __restrict vlSymsp) VL_ATTR_COLD;
    static void _sequent__TOP__1(VvPrescaler__Syms* __restrict vlSymsp);
    static void _settle__TOP__2(VvPrescaler__Syms* __restrict vlSymsp);
} VL_ATTR_ALIGNED(VL_CACHE_LINE_BYTES);

//----------


#endif  // guard
