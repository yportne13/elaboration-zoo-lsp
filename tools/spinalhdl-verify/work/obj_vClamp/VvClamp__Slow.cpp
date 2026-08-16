// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See VvClamp.h for the primary calling header

#include "VvClamp.h"
#include "VvClamp__Syms.h"

//==========

VL_CTOR_IMP(VvClamp) {
    VvClamp__Syms* __restrict vlSymsp = __VlSymsp = new VvClamp__Syms(this, name());
    VvClamp* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Reset internal values
    
    // Reset structure values
    _ctor_var_reset();
}

void VvClamp::__Vconfigure(VvClamp__Syms* vlSymsp, bool first) {
    if (false && first) {}  // Prevent unused
    this->__VlSymsp = vlSymsp;
    if (false && this->__VlSymsp) {}  // Prevent unused
    Verilated::timeunit(-12);
    Verilated::timeprecision(-12);
}

VvClamp::~VvClamp() {
    VL_DO_CLEAR(delete __VlSymsp, __VlSymsp = NULL);
}

void VvClamp::_eval_initial(VvClamp__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvClamp::_eval_initial\n"); );
    VvClamp* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
}

void VvClamp::final() {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvClamp::final\n"); );
    // Variables
    VvClamp__Syms* __restrict vlSymsp = this->__VlSymsp;
    VvClamp* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
}

void VvClamp::_eval_settle(VvClamp__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvClamp::_eval_settle\n"); );
    VvClamp* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    vlTOPp->_combo__TOP__1(vlSymsp);
}

void VvClamp::_ctor_var_reset() {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvClamp::_ctor_var_reset\n"); );
    // Body
    a = VL_RAND_RESET_I(8);
    lo = VL_RAND_RESET_I(8);
    hi = VL_RAND_RESET_I(8);
    cl = VL_RAND_RESET_I(8);
}
