// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See VvEndianSwap.h for the primary calling header

#include "VvEndianSwap.h"
#include "VvEndianSwap__Syms.h"

//==========

VL_CTOR_IMP(VvEndianSwap) {
    VvEndianSwap__Syms* __restrict vlSymsp = __VlSymsp = new VvEndianSwap__Syms(this, name());
    VvEndianSwap* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Reset internal values
    
    // Reset structure values
    _ctor_var_reset();
}

void VvEndianSwap::__Vconfigure(VvEndianSwap__Syms* vlSymsp, bool first) {
    if (false && first) {}  // Prevent unused
    this->__VlSymsp = vlSymsp;
    if (false && this->__VlSymsp) {}  // Prevent unused
    Verilated::timeunit(-12);
    Verilated::timeprecision(-12);
}

VvEndianSwap::~VvEndianSwap() {
    VL_DO_CLEAR(delete __VlSymsp, __VlSymsp = NULL);
}

void VvEndianSwap::_eval_initial(VvEndianSwap__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvEndianSwap::_eval_initial\n"); );
    VvEndianSwap* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
}

void VvEndianSwap::final() {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvEndianSwap::final\n"); );
    // Variables
    VvEndianSwap__Syms* __restrict vlSymsp = this->__VlSymsp;
    VvEndianSwap* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
}

void VvEndianSwap::_eval_settle(VvEndianSwap__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvEndianSwap::_eval_settle\n"); );
    VvEndianSwap* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    vlTOPp->_combo__TOP__1(vlSymsp);
}

void VvEndianSwap::_ctor_var_reset() {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvEndianSwap::_ctor_var_reset\n"); );
    // Body
    a = VL_RAND_RESET_I(16);
    s = VL_RAND_RESET_I(16);
}
