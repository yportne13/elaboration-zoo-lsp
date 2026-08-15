// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See VvStreamFifo.h for the primary calling header

#include "VvStreamFifo.h"
#include "VvStreamFifo__Syms.h"

//==========

VL_CTOR_IMP(VvStreamFifo) {
    VvStreamFifo__Syms* __restrict vlSymsp = __VlSymsp = new VvStreamFifo__Syms(this, name());
    VvStreamFifo* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Reset internal values
    
    // Reset structure values
    _ctor_var_reset();
}

void VvStreamFifo::__Vconfigure(VvStreamFifo__Syms* vlSymsp, bool first) {
    if (false && first) {}  // Prevent unused
    this->__VlSymsp = vlSymsp;
    if (false && this->__VlSymsp) {}  // Prevent unused
    Verilated::timeunit(-12);
    Verilated::timeprecision(-12);
}

VvStreamFifo::~VvStreamFifo() {
    VL_DO_CLEAR(delete __VlSymsp, __VlSymsp = NULL);
}

void VvStreamFifo::_settle__TOP__2(VvStreamFifo__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvStreamFifo::_settle__TOP__2\n"); );
    VvStreamFifo* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    vlTOPp->pop_payload = vlTOPp->vStreamFifo__DOT__fifo_mem
        [(3U & (IData)(vlTOPp->vStreamFifo__DOT__fifo_ptrPop))];
    vlTOPp->occ = (7U & ((IData)(vlTOPp->vStreamFifo__DOT__fifo_ptrPush) 
                         - (IData)(vlTOPp->vStreamFifo__DOT__fifo_ptrPop)));
    vlTOPp->vStreamFifo__DOT__fifo_push_ready = (4U 
                                                 != 
                                                 ((IData)(vlTOPp->vStreamFifo__DOT__fifo_ptrPush) 
                                                  ^ (IData)(vlTOPp->vStreamFifo__DOT__fifo_ptrPop)));
    vlTOPp->vStreamFifo__DOT__fifo_pop_valid = ((IData)(vlTOPp->vStreamFifo__DOT__fifo_ptrPush) 
                                                != (IData)(vlTOPp->vStreamFifo__DOT__fifo_ptrPop));
    vlTOPp->push_ready = vlTOPp->vStreamFifo__DOT__fifo_push_ready;
    vlTOPp->pop_valid = vlTOPp->vStreamFifo__DOT__fifo_pop_valid;
}

void VvStreamFifo::_eval_initial(VvStreamFifo__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvStreamFifo::_eval_initial\n"); );
    VvStreamFifo* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    vlTOPp->__Vclklast__TOP__clk = vlTOPp->clk;
    vlTOPp->__Vclklast__TOP__reset = vlTOPp->reset;
}

void VvStreamFifo::final() {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvStreamFifo::final\n"); );
    // Variables
    VvStreamFifo__Syms* __restrict vlSymsp = this->__VlSymsp;
    VvStreamFifo* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
}

void VvStreamFifo::_eval_settle(VvStreamFifo__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvStreamFifo::_eval_settle\n"); );
    VvStreamFifo* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    vlTOPp->_settle__TOP__2(vlSymsp);
}

void VvStreamFifo::_ctor_var_reset() {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvStreamFifo::_ctor_var_reset\n"); );
    // Body
    push_valid = VL_RAND_RESET_I(1);
    push_payload = VL_RAND_RESET_I(8);
    push_ready = VL_RAND_RESET_I(1);
    pop_valid = VL_RAND_RESET_I(1);
    pop_ready = VL_RAND_RESET_I(1);
    pop_payload = VL_RAND_RESET_I(8);
    occ = VL_RAND_RESET_I(3);
    clk = VL_RAND_RESET_I(1);
    reset = VL_RAND_RESET_I(1);
    vStreamFifo__DOT__fifo_push_ready = VL_RAND_RESET_I(1);
    vStreamFifo__DOT__fifo_pop_valid = VL_RAND_RESET_I(1);
    vStreamFifo__DOT__fifo_ptrPush = VL_RAND_RESET_I(3);
    vStreamFifo__DOT__fifo_ptrPop = VL_RAND_RESET_I(3);
    { int __Vi0=0; for (; __Vi0<4; ++__Vi0) {
            vStreamFifo__DOT__fifo_mem[__Vi0] = VL_RAND_RESET_I(8);
    }}
}
