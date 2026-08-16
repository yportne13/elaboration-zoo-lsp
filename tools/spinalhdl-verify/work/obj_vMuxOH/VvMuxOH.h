// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Primary design header
//
// This header should be included by all source files instantiating the design.
// The class here is then constructed to instantiate the design.
// See the Verilator manual for examples.

#ifndef _VVMUXOH_H_
#define _VVMUXOH_H_  // guard

#include "verilated.h"

//==========

class VvMuxOH__Syms;

//----------

VL_MODULE(VvMuxOH) {
  public:
    
    // PORTS
    // The application code writes and reads these signals to
    // propagate new values into/out from the Verilated model.
    VL_IN8(sel,3,0);
    VL_IN8(a,7,0);
    VL_IN8(b,7,0);
    VL_IN8(c,7,0);
    VL_IN8(d,7,0);
    VL_OUT8(o,7,0);
    
    // INTERNAL VARIABLES
    // Internals; generally not touched by application code
    VvMuxOH__Syms* __VlSymsp;  // Symbol table
    
    // CONSTRUCTORS
  private:
    VL_UNCOPYABLE(VvMuxOH);  ///< Copying not allowed
  public:
    /// Construct the model; called by application code
    /// The special name  may be used to make a wrapper with a
    /// single model invisible with respect to DPI scope names.
    VvMuxOH(const char* name = "TOP");
    /// Destroy the model; called (often implicitly) by application code
    ~VvMuxOH();
    
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
    static void _eval_initial_loop(VvMuxOH__Syms* __restrict vlSymsp);
  public:
    void __Vconfigure(VvMuxOH__Syms* symsp, bool first);
  private:
    static QData _change_request(VvMuxOH__Syms* __restrict vlSymsp);
    static QData _change_request_1(VvMuxOH__Syms* __restrict vlSymsp);
  public:
    static void _combo__TOP__1(VvMuxOH__Syms* __restrict vlSymsp);
  private:
    void _ctor_var_reset() VL_ATTR_COLD;
  public:
    static void _eval(VvMuxOH__Syms* __restrict vlSymsp);
  private:
#ifdef VL_DEBUG
    void _eval_debug_assertions();
#endif  // VL_DEBUG
  public:
    static void _eval_initial(VvMuxOH__Syms* __restrict vlSymsp) VL_ATTR_COLD;
    static void _eval_settle(VvMuxOH__Syms* __restrict vlSymsp) VL_ATTR_COLD;
} VL_ATTR_ALIGNED(VL_CACHE_LINE_BYTES);

//----------


#endif  // guard
