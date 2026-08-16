// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See VvWatchdog.h for the primary calling header

#include "VvWatchdog.h"
#include "VvWatchdog__Syms.h"

//==========

VL_CTOR_IMP(VvWatchdog) {
    VvWatchdog__Syms* __restrict vlSymsp = __VlSymsp = new VvWatchdog__Syms(this, name());
    VvWatchdog* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Reset internal values
    
    // Reset structure values
    _ctor_var_reset();
}

void VvWatchdog::__Vconfigure(VvWatchdog__Syms* vlSymsp, bool first) {
    if (false && first) {}  // Prevent unused
    this->__VlSymsp = vlSymsp;
    if (false && this->__VlSymsp) {}  // Prevent unused
    Verilated::timeunit(-12);
    Verilated::timeprecision(-12);
}

VvWatchdog::~VvWatchdog() {
    VL_DO_CLEAR(delete __VlSymsp, __VlSymsp = NULL);
}

void VvWatchdog::_settle__TOP__2(VvWatchdog__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvWatchdog::_settle__TOP__2\n"); );
    VvWatchdog* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    vlTOPp->timeout = vlTOPp->vWatchdog__DOT_____05Ftimeout;
}

void VvWatchdog::_eval_initial(VvWatchdog__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvWatchdog::_eval_initial\n"); );
    VvWatchdog* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    vlTOPp->__Vclklast__TOP__clk = vlTOPp->clk;
    vlTOPp->__Vclklast__TOP__reset = vlTOPp->reset;
}

void VvWatchdog::final() {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvWatchdog::final\n"); );
    // Variables
    VvWatchdog__Syms* __restrict vlSymsp = this->__VlSymsp;
    VvWatchdog* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
}

void VvWatchdog::_eval_settle(VvWatchdog__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvWatchdog::_eval_settle\n"); );
    VvWatchdog* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    vlTOPp->_settle__TOP__2(vlSymsp);
}

void VvWatchdog::_ctor_var_reset() {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvWatchdog::_ctor_var_reset\n"); );
    // Body
    feed = VL_RAND_RESET_I(1);
    lim = VL_RAND_RESET_I(8);
    timeout = VL_RAND_RESET_I(1);
    clk = VL_RAND_RESET_I(1);
    reset = VL_RAND_RESET_I(1);
    vWatchdog__DOT_____05Fcnt = VL_RAND_RESET_I(8);
    vWatchdog__DOT_____05Ftimeout = VL_RAND_RESET_I(1);
}
