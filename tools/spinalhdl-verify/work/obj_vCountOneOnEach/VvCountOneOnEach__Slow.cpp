// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See VvCountOneOnEach.h for the primary calling header

#include "VvCountOneOnEach.h"
#include "VvCountOneOnEach__Syms.h"

//==========

VL_CTOR_IMP(VvCountOneOnEach) {
    VvCountOneOnEach__Syms* __restrict vlSymsp = __VlSymsp = new VvCountOneOnEach__Syms(this, name());
    VvCountOneOnEach* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Reset internal values
    
    // Reset structure values
    _ctor_var_reset();
}

void VvCountOneOnEach::__Vconfigure(VvCountOneOnEach__Syms* vlSymsp, bool first) {
    if (false && first) {}  // Prevent unused
    this->__VlSymsp = vlSymsp;
    if (false && this->__VlSymsp) {}  // Prevent unused
    Verilated::timeunit(-12);
    Verilated::timeprecision(-12);
}

VvCountOneOnEach::~VvCountOneOnEach() {
    VL_DO_CLEAR(delete __VlSymsp, __VlSymsp = NULL);
}

void VvCountOneOnEach::_eval_initial(VvCountOneOnEach__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvCountOneOnEach::_eval_initial\n"); );
    VvCountOneOnEach* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
}

void VvCountOneOnEach::final() {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvCountOneOnEach::final\n"); );
    // Variables
    VvCountOneOnEach__Syms* __restrict vlSymsp = this->__VlSymsp;
    VvCountOneOnEach* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
}

void VvCountOneOnEach::_eval_settle(VvCountOneOnEach__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvCountOneOnEach::_eval_settle\n"); );
    VvCountOneOnEach* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    vlTOPp->_combo__TOP__1(vlSymsp);
}

void VvCountOneOnEach::_ctor_var_reset() {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvCountOneOnEach::_ctor_var_reset\n"); );
    // Body
    a = VL_RAND_RESET_I(4);
    c1 = VL_RAND_RESET_I(3);
    c2 = VL_RAND_RESET_I(3);
    c3 = VL_RAND_RESET_I(3);
    c4 = VL_RAND_RESET_I(3);
}
