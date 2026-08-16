// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See VvTimer.h for the primary calling header

#include "VvTimer.h"
#include "VvTimer__Syms.h"

//==========

VL_CTOR_IMP(VvTimer) {
    VvTimer__Syms* __restrict vlSymsp = __VlSymsp = new VvTimer__Syms(this, name());
    VvTimer* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Reset internal values
    
    // Reset structure values
    _ctor_var_reset();
}

void VvTimer::__Vconfigure(VvTimer__Syms* vlSymsp, bool first) {
    if (false && first) {}  // Prevent unused
    this->__VlSymsp = vlSymsp;
    if (false && this->__VlSymsp) {}  // Prevent unused
    Verilated::timeunit(-12);
    Verilated::timeprecision(-12);
}

VvTimer::~VvTimer() {
    VL_DO_CLEAR(delete __VlSymsp, __VlSymsp = NULL);
}

void VvTimer::_settle__TOP__2(VvTimer__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvTimer::_settle__TOP__2\n"); );
    VvTimer* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    vlTOPp->value = vlTOPp->vTimer__DOT__t_cnt;
    vlTOPp->full = ((((IData)(vlTOPp->vTimer__DOT__t_cnt) 
                      == (IData)(vlTOPp->lim)) & (IData)(vlTOPp->tick)) 
                    & (~ (IData)(vlTOPp->vTimer__DOT__t_inhibit)));
}

void VvTimer::_eval_initial(VvTimer__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvTimer::_eval_initial\n"); );
    VvTimer* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    vlTOPp->__Vclklast__TOP__clk = vlTOPp->clk;
    vlTOPp->__Vclklast__TOP__reset = vlTOPp->reset;
}

void VvTimer::final() {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvTimer::final\n"); );
    // Variables
    VvTimer__Syms* __restrict vlSymsp = this->__VlSymsp;
    VvTimer* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
}

void VvTimer::_eval_settle(VvTimer__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvTimer::_eval_settle\n"); );
    VvTimer* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    vlTOPp->_settle__TOP__2(vlSymsp);
}

void VvTimer::_ctor_var_reset() {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvTimer::_ctor_var_reset\n"); );
    // Body
    tick = VL_RAND_RESET_I(1);
    clr = VL_RAND_RESET_I(1);
    lim = VL_RAND_RESET_I(8);
    full = VL_RAND_RESET_I(1);
    value = VL_RAND_RESET_I(8);
    clk = VL_RAND_RESET_I(1);
    reset = VL_RAND_RESET_I(1);
    vTimer__DOT__t_cnt = VL_RAND_RESET_I(8);
    vTimer__DOT__t_inhibit = VL_RAND_RESET_I(1);
}
