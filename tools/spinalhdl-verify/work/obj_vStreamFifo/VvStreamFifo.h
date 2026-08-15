// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Primary design header
//
// This header should be included by all source files instantiating the design.
// The class here is then constructed to instantiate the design.
// See the Verilator manual for examples.

#ifndef _VVSTREAMFIFO_H_
#define _VVSTREAMFIFO_H_  // guard

#include "verilated.h"

//==========

class VvStreamFifo__Syms;

//----------

VL_MODULE(VvStreamFifo) {
  public:
    
    // PORTS
    // The application code writes and reads these signals to
    // propagate new values into/out from the Verilated model.
    VL_IN8(clk,0,0);
    VL_IN8(reset,0,0);
    VL_IN8(push_valid,0,0);
    VL_IN8(push_payload,7,0);
    VL_OUT8(push_ready,0,0);
    VL_OUT8(pop_valid,0,0);
    VL_IN8(pop_ready,0,0);
    VL_OUT8(pop_payload,7,0);
    VL_OUT8(occ,2,0);
    
    // LOCAL SIGNALS
    // Internals; generally not touched by application code
    CData/*0:0*/ vStreamFifo__DOT__fifo_push_ready;
    CData/*0:0*/ vStreamFifo__DOT__fifo_pop_valid;
    CData/*2:0*/ vStreamFifo__DOT__fifo_ptrPush;
    CData/*2:0*/ vStreamFifo__DOT__fifo_ptrPop;
    CData/*7:0*/ vStreamFifo__DOT__fifo_mem[4];
    
    // LOCAL VARIABLES
    // Internals; generally not touched by application code
    CData/*0:0*/ __Vclklast__TOP__clk;
    CData/*0:0*/ __Vclklast__TOP__reset;
    
    // INTERNAL VARIABLES
    // Internals; generally not touched by application code
    VvStreamFifo__Syms* __VlSymsp;  // Symbol table
    
    // CONSTRUCTORS
  private:
    VL_UNCOPYABLE(VvStreamFifo);  ///< Copying not allowed
  public:
    /// Construct the model; called by application code
    /// The special name  may be used to make a wrapper with a
    /// single model invisible with respect to DPI scope names.
    VvStreamFifo(const char* name = "TOP");
    /// Destroy the model; called (often implicitly) by application code
    ~VvStreamFifo();
    
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
    static void _eval_initial_loop(VvStreamFifo__Syms* __restrict vlSymsp);
  public:
    void __Vconfigure(VvStreamFifo__Syms* symsp, bool first);
  private:
    static QData _change_request(VvStreamFifo__Syms* __restrict vlSymsp);
    static QData _change_request_1(VvStreamFifo__Syms* __restrict vlSymsp);
    void _ctor_var_reset() VL_ATTR_COLD;
  public:
    static void _eval(VvStreamFifo__Syms* __restrict vlSymsp);
  private:
#ifdef VL_DEBUG
    void _eval_debug_assertions();
#endif  // VL_DEBUG
  public:
    static void _eval_initial(VvStreamFifo__Syms* __restrict vlSymsp) VL_ATTR_COLD;
    static void _eval_settle(VvStreamFifo__Syms* __restrict vlSymsp) VL_ATTR_COLD;
    static void _sequent__TOP__1(VvStreamFifo__Syms* __restrict vlSymsp);
    static void _settle__TOP__2(VvStreamFifo__Syms* __restrict vlSymsp) VL_ATTR_COLD;
} VL_ATTR_ALIGNED(VL_CACHE_LINE_BYTES);

//----------


#endif  // guard
