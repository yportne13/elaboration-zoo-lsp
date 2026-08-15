// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See VvDownCounter.h for the primary calling header

#include "VvDownCounter.h"
#include "VvDownCounter__Syms.h"

//==========

VL_CTOR_IMP(VvDownCounter) {
    VvDownCounter__Syms* __restrict vlSymsp = __VlSymsp = new VvDownCounter__Syms(this, name());
    VvDownCounter* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Reset internal values
    
    // Reset structure values
    _ctor_var_reset();
}

void VvDownCounter::__Vconfigure(VvDownCounter__Syms* vlSymsp, bool first) {
    if (false && first) {}  // Prevent unused
    this->__VlSymsp = vlSymsp;
    if (false && this->__VlSymsp) {}  // Prevent unused
    Verilated::timeunit(-12);
    Verilated::timeprecision(-12);
}

VvDownCounter::~VvDownCounter() {
    VL_DO_CLEAR(delete __VlSymsp, __VlSymsp = NULL);
}

void VvDownCounter::_settle__TOP__2(VvDownCounter__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvDownCounter::_settle__TOP__2\n"); );
    VvDownCounter* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    vlTOPp->value = vlTOPp->vDownCounter__DOT__dc;
    vlTOPp->willOverflow = (0U == (IData)(vlTOPp->vDownCounter__DOT__dc));
}

void VvDownCounter::_eval_initial(VvDownCounter__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvDownCounter::_eval_initial\n"); );
    VvDownCounter* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    vlTOPp->__Vclklast__TOP__clk = vlTOPp->clk;
    vlTOPp->__Vclklast__TOP__reset = vlTOPp->reset;
}

void VvDownCounter::final() {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvDownCounter::final\n"); );
    // Variables
    VvDownCounter__Syms* __restrict vlSymsp = this->__VlSymsp;
    VvDownCounter* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
}

void VvDownCounter::_eval_settle(VvDownCounter__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvDownCounter::_eval_settle\n"); );
    VvDownCounter* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    vlTOPp->_settle__TOP__2(vlSymsp);
}

void VvDownCounter::_ctor_var_reset() {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvDownCounter::_ctor_var_reset\n"); );
    // Body
    en = VL_RAND_RESET_I(1);
    value = VL_RAND_RESET_I(4);
    willOverflow = VL_RAND_RESET_I(1);
    clk = VL_RAND_RESET_I(1);
    reset = VL_RAND_RESET_I(1);
    vDownCounter__DOT__dc = VL_RAND_RESET_I(4);
}
