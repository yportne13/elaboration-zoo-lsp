// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See VvTimeout.h for the primary calling header

#include "VvTimeout.h"
#include "VvTimeout__Syms.h"

//==========

VL_CTOR_IMP(VvTimeout) {
    VvTimeout__Syms* __restrict vlSymsp = __VlSymsp = new VvTimeout__Syms(this, name());
    VvTimeout* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Reset internal values
    
    // Reset structure values
    _ctor_var_reset();
}

void VvTimeout::__Vconfigure(VvTimeout__Syms* vlSymsp, bool first) {
    if (false && first) {}  // Prevent unused
    this->__VlSymsp = vlSymsp;
    if (false && this->__VlSymsp) {}  // Prevent unused
    Verilated::timeunit(-12);
    Verilated::timeprecision(-12);
}

VvTimeout::~VvTimeout() {
    VL_DO_CLEAR(delete __VlSymsp, __VlSymsp = NULL);
}

void VvTimeout::_settle__TOP__2(VvTimeout__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvTimeout::_settle__TOP__2\n"); );
    VvTimeout* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    vlTOPp->ts = vlTOPp->vTimeout__DOT__t;
}

void VvTimeout::_eval_initial(VvTimeout__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvTimeout::_eval_initial\n"); );
    VvTimeout* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    vlTOPp->__Vclklast__TOP__clk = vlTOPp->clk;
    vlTOPp->__Vclklast__TOP__reset = vlTOPp->reset;
}

void VvTimeout::final() {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvTimeout::final\n"); );
    // Variables
    VvTimeout__Syms* __restrict vlSymsp = this->__VlSymsp;
    VvTimeout* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
}

void VvTimeout::_eval_settle(VvTimeout__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvTimeout::_eval_settle\n"); );
    VvTimeout* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    vlTOPp->_settle__TOP__2(vlSymsp);
}

void VvTimeout::_ctor_var_reset() {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvTimeout::_ctor_var_reset\n"); );
    // Body
    en = VL_RAND_RESET_I(1);
    ts = VL_RAND_RESET_I(1);
    clk = VL_RAND_RESET_I(1);
    reset = VL_RAND_RESET_I(1);
    vTimeout__DOT__t = VL_RAND_RESET_I(1);
    vTimeout__DOT__t_cnt = VL_RAND_RESET_I(3);
}
