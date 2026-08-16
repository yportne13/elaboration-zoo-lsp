// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See VvPrescaler.h for the primary calling header

#include "VvPrescaler.h"
#include "VvPrescaler__Syms.h"

//==========

VL_CTOR_IMP(VvPrescaler) {
    VvPrescaler__Syms* __restrict vlSymsp = __VlSymsp = new VvPrescaler__Syms(this, name());
    VvPrescaler* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Reset internal values
    
    // Reset structure values
    _ctor_var_reset();
}

void VvPrescaler::__Vconfigure(VvPrescaler__Syms* vlSymsp, bool first) {
    if (false && first) {}  // Prevent unused
    this->__VlSymsp = vlSymsp;
    if (false && this->__VlSymsp) {}  // Prevent unused
    Verilated::timeunit(-12);
    Verilated::timeprecision(-12);
}

VvPrescaler::~VvPrescaler() {
    VL_DO_CLEAR(delete __VlSymsp, __VlSymsp = NULL);
}

void VvPrescaler::_eval_initial(VvPrescaler__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvPrescaler::_eval_initial\n"); );
    VvPrescaler* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    vlTOPp->__Vclklast__TOP__clk = vlTOPp->clk;
    vlTOPp->__Vclklast__TOP__reset = vlTOPp->reset;
}

void VvPrescaler::final() {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvPrescaler::final\n"); );
    // Variables
    VvPrescaler__Syms* __restrict vlSymsp = this->__VlSymsp;
    VvPrescaler* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
}

void VvPrescaler::_eval_settle(VvPrescaler__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvPrescaler::_eval_settle\n"); );
    VvPrescaler* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    vlTOPp->_settle__TOP__2(vlSymsp);
}

void VvPrescaler::_ctor_var_reset() {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvPrescaler::_ctor_var_reset\n"); );
    // Body
    lim = VL_RAND_RESET_I(8);
    ov = VL_RAND_RESET_I(1);
    clk = VL_RAND_RESET_I(1);
    reset = VL_RAND_RESET_I(1);
    vPrescaler__DOT__p_cnt = VL_RAND_RESET_I(8);
}
