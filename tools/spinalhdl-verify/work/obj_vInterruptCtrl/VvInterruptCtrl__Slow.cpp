// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See VvInterruptCtrl.h for the primary calling header

#include "VvInterruptCtrl.h"
#include "VvInterruptCtrl__Syms.h"

//==========

VL_CTOR_IMP(VvInterruptCtrl) {
    VvInterruptCtrl__Syms* __restrict vlSymsp = __VlSymsp = new VvInterruptCtrl__Syms(this, name());
    VvInterruptCtrl* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Reset internal values
    
    // Reset structure values
    _ctor_var_reset();
}

void VvInterruptCtrl::__Vconfigure(VvInterruptCtrl__Syms* vlSymsp, bool first) {
    if (false && first) {}  // Prevent unused
    this->__VlSymsp = vlSymsp;
    if (false && this->__VlSymsp) {}  // Prevent unused
    Verilated::timeunit(-12);
    Verilated::timeprecision(-12);
}

VvInterruptCtrl::~VvInterruptCtrl() {
    VL_DO_CLEAR(delete __VlSymsp, __VlSymsp = NULL);
}

void VvInterruptCtrl::_eval_initial(VvInterruptCtrl__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvInterruptCtrl::_eval_initial\n"); );
    VvInterruptCtrl* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    vlTOPp->__Vclklast__TOP__clk = vlTOPp->clk;
    vlTOPp->__Vclklast__TOP__reset = vlTOPp->reset;
}

void VvInterruptCtrl::final() {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvInterruptCtrl::final\n"); );
    // Variables
    VvInterruptCtrl__Syms* __restrict vlSymsp = this->__VlSymsp;
    VvInterruptCtrl* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
}

void VvInterruptCtrl::_eval_settle(VvInterruptCtrl__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvInterruptCtrl::_eval_settle\n"); );
    VvInterruptCtrl* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    vlTOPp->_settle__TOP__2(vlSymsp);
}

void VvInterruptCtrl::_ctor_var_reset() {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvInterruptCtrl::_ctor_var_reset\n"); );
    // Body
    inputs = VL_RAND_RESET_I(4);
    clears = VL_RAND_RESET_I(4);
    masks = VL_RAND_RESET_I(4);
    pend = VL_RAND_RESET_I(4);
    clk = VL_RAND_RESET_I(1);
    reset = VL_RAND_RESET_I(1);
    vInterruptCtrl__DOT_____05Fpend = VL_RAND_RESET_I(4);
}
