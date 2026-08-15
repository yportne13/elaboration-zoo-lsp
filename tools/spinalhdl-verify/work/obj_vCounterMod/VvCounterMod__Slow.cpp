// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See VvCounterMod.h for the primary calling header

#include "VvCounterMod.h"
#include "VvCounterMod__Syms.h"

//==========

VL_CTOR_IMP(VvCounterMod) {
    VvCounterMod__Syms* __restrict vlSymsp = __VlSymsp = new VvCounterMod__Syms(this, name());
    VvCounterMod* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Reset internal values
    
    // Reset structure values
    _ctor_var_reset();
}

void VvCounterMod::__Vconfigure(VvCounterMod__Syms* vlSymsp, bool first) {
    if (false && first) {}  // Prevent unused
    this->__VlSymsp = vlSymsp;
    if (false && this->__VlSymsp) {}  // Prevent unused
    Verilated::timeunit(-12);
    Verilated::timeprecision(-12);
}

VvCounterMod::~VvCounterMod() {
    VL_DO_CLEAR(delete __VlSymsp, __VlSymsp = NULL);
}

void VvCounterMod::_settle__TOP__2(VvCounterMod__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvCounterMod::_settle__TOP__2\n"); );
    VvCounterMod* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    vlTOPp->value = vlTOPp->vCounterMod__DOT__cm;
    vlTOPp->willOverflow = (9U == (IData)(vlTOPp->vCounterMod__DOT__cm));
}

void VvCounterMod::_eval_initial(VvCounterMod__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvCounterMod::_eval_initial\n"); );
    VvCounterMod* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    vlTOPp->__Vclklast__TOP__clk = vlTOPp->clk;
    vlTOPp->__Vclklast__TOP__reset = vlTOPp->reset;
}

void VvCounterMod::final() {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvCounterMod::final\n"); );
    // Variables
    VvCounterMod__Syms* __restrict vlSymsp = this->__VlSymsp;
    VvCounterMod* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
}

void VvCounterMod::_eval_settle(VvCounterMod__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvCounterMod::_eval_settle\n"); );
    VvCounterMod* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    vlTOPp->_settle__TOP__2(vlSymsp);
}

void VvCounterMod::_ctor_var_reset() {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvCounterMod::_ctor_var_reset\n"); );
    // Body
    en = VL_RAND_RESET_I(1);
    value = VL_RAND_RESET_I(4);
    willOverflow = VL_RAND_RESET_I(1);
    clk = VL_RAND_RESET_I(1);
    reset = VL_RAND_RESET_I(1);
    vCounterMod__DOT__cm = VL_RAND_RESET_I(4);
}
