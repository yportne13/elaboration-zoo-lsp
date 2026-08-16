// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Primary design header
//
// This header should be included by all source files instantiating the design.
// The class here is then constructed to instantiate the design.
// See the Verilator manual for examples.

#ifndef _VVPULSECC_H_
#define _VVPULSECC_H_  // guard

#include "verilated.h"

//==========

class VvPulseCC__Syms;

//----------

VL_MODULE(VvPulseCC) {
  public:
    
    // PORTS
    // The application code writes and reads these signals to
    // propagate new values into/out from the Verilated model.
    VL_IN8(clkA,0,0);
    VL_IN8(clkB,0,0);
    VL_IN8(pulseIn,0,0);
    VL_OUT8(pulseOut,0,0);
    
    // LOCAL SIGNALS
    // Internals; generally not touched by application code
    CData/*0:0*/ vPulseCC__DOT_____05Ftoggle;
    CData/*0:0*/ vPulseCC__DOT_____05Fsync1;
    CData/*0:0*/ vPulseCC__DOT_____05Fsync2;
    
    // LOCAL VARIABLES
    // Internals; generally not touched by application code
    CData/*0:0*/ __Vdly__vPulseCC__DOT_____05Ftoggle;
    CData/*0:0*/ __Vclklast__TOP__clkA;
    CData/*0:0*/ __Vclklast__TOP__clkB;
    
    // INTERNAL VARIABLES
    // Internals; generally not touched by application code
    VvPulseCC__Syms* __VlSymsp;  // Symbol table
    
    // CONSTRUCTORS
  private:
    VL_UNCOPYABLE(VvPulseCC);  ///< Copying not allowed
  public:
    /// Construct the model; called by application code
    /// The special name  may be used to make a wrapper with a
    /// single model invisible with respect to DPI scope names.
    VvPulseCC(const char* name = "TOP");
    /// Destroy the model; called (often implicitly) by application code
    ~VvPulseCC();
    
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
    static void _eval_initial_loop(VvPulseCC__Syms* __restrict vlSymsp);
  public:
    void __Vconfigure(VvPulseCC__Syms* symsp, bool first);
  private:
    static QData _change_request(VvPulseCC__Syms* __restrict vlSymsp);
    static QData _change_request_1(VvPulseCC__Syms* __restrict vlSymsp);
    void _ctor_var_reset() VL_ATTR_COLD;
  public:
    static void _eval(VvPulseCC__Syms* __restrict vlSymsp);
  private:
#ifdef VL_DEBUG
    void _eval_debug_assertions();
#endif  // VL_DEBUG
  public:
    static void _eval_initial(VvPulseCC__Syms* __restrict vlSymsp) VL_ATTR_COLD;
    static void _eval_settle(VvPulseCC__Syms* __restrict vlSymsp) VL_ATTR_COLD;
    static void _sequent__TOP__1(VvPulseCC__Syms* __restrict vlSymsp);
    static void _sequent__TOP__2(VvPulseCC__Syms* __restrict vlSymsp);
    static void _sequent__TOP__4(VvPulseCC__Syms* __restrict vlSymsp);
    static void _settle__TOP__3(VvPulseCC__Syms* __restrict vlSymsp) VL_ATTR_COLD;
} VL_ATTR_ALIGNED(VL_CACHE_LINE_BYTES);

//----------


#endif  // guard
