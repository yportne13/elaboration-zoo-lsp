// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See VvReverse.h for the primary calling header

#include "VvReverse.h"
#include "VvReverse__Syms.h"

//==========

VL_CTOR_IMP(VvReverse) {
    VvReverse__Syms* __restrict vlSymsp = __VlSymsp = new VvReverse__Syms(this, name());
    VvReverse* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Reset internal values
    
    // Reset structure values
    _ctor_var_reset();
}

void VvReverse::__Vconfigure(VvReverse__Syms* vlSymsp, bool first) {
    if (false && first) {}  // Prevent unused
    this->__VlSymsp = vlSymsp;
    if (false && this->__VlSymsp) {}  // Prevent unused
    Verilated::timeunit(-12);
    Verilated::timeprecision(-12);
}

VvReverse::~VvReverse() {
    VL_DO_CLEAR(delete __VlSymsp, __VlSymsp = NULL);
}

void VvReverse::_eval_initial(VvReverse__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvReverse::_eval_initial\n"); );
    VvReverse* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
}

void VvReverse::final() {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvReverse::final\n"); );
    // Variables
    VvReverse__Syms* __restrict vlSymsp = this->__VlSymsp;
    VvReverse* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
}

void VvReverse::_eval_settle(VvReverse__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvReverse::_eval_settle\n"); );
    VvReverse* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    vlTOPp->_combo__TOP__1(vlSymsp);
}

void VvReverse::_ctor_var_reset() {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvReverse::_ctor_var_reset\n"); );
    // Body
    a = VL_RAND_RESET_I(8);
    r = VL_RAND_RESET_I(8);
}
