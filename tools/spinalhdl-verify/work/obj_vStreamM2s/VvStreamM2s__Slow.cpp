// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See VvStreamM2s.h for the primary calling header

#include "VvStreamM2s.h"
#include "VvStreamM2s__Syms.h"

//==========

VL_CTOR_IMP(VvStreamM2s) {
    VvStreamM2s__Syms* __restrict vlSymsp = __VlSymsp = new VvStreamM2s__Syms(this, name());
    VvStreamM2s* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Reset internal values
    
    // Reset structure values
    _ctor_var_reset();
}

void VvStreamM2s::__Vconfigure(VvStreamM2s__Syms* vlSymsp, bool first) {
    if (false && first) {}  // Prevent unused
    this->__VlSymsp = vlSymsp;
    if (false && this->__VlSymsp) {}  // Prevent unused
    Verilated::timeunit(-12);
    Verilated::timeprecision(-12);
}

VvStreamM2s::~VvStreamM2s() {
    VL_DO_CLEAR(delete __VlSymsp, __VlSymsp = NULL);
}

void VvStreamM2s::_settle__TOP__2(VvStreamM2s__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvStreamM2s::_settle__TOP__2\n"); );
    VvStreamM2s* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    vlTOPp->pop_valid = vlTOPp->vStreamM2s__DOT__piped_valid;
    vlTOPp->pop_payload = vlTOPp->vStreamM2s__DOT__piped_data;
    vlTOPp->push_ready = ((IData)(vlTOPp->vStreamM2s__DOT__piped_valid) 
                          | (IData)(vlTOPp->pop_ready));
}

void VvStreamM2s::_eval_initial(VvStreamM2s__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvStreamM2s::_eval_initial\n"); );
    VvStreamM2s* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    vlTOPp->__Vclklast__TOP__clk = vlTOPp->clk;
    vlTOPp->__Vclklast__TOP__reset = vlTOPp->reset;
}

void VvStreamM2s::final() {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvStreamM2s::final\n"); );
    // Variables
    VvStreamM2s__Syms* __restrict vlSymsp = this->__VlSymsp;
    VvStreamM2s* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
}

void VvStreamM2s::_eval_settle(VvStreamM2s__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvStreamM2s::_eval_settle\n"); );
    VvStreamM2s* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    vlTOPp->_settle__TOP__2(vlSymsp);
}

void VvStreamM2s::_ctor_var_reset() {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvStreamM2s::_ctor_var_reset\n"); );
    // Body
    push_valid = VL_RAND_RESET_I(1);
    push_payload = VL_RAND_RESET_I(8);
    push_ready = VL_RAND_RESET_I(1);
    pop_valid = VL_RAND_RESET_I(1);
    pop_ready = VL_RAND_RESET_I(1);
    pop_payload = VL_RAND_RESET_I(8);
    clk = VL_RAND_RESET_I(1);
    reset = VL_RAND_RESET_I(1);
    vStreamM2s__DOT__piped_valid = VL_RAND_RESET_I(1);
    vStreamM2s__DOT__piped_data = VL_RAND_RESET_I(8);
}
