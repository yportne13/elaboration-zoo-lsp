// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See VvMajority.h for the primary calling header

#include "VvMajority.h"
#include "VvMajority__Syms.h"

//==========

VL_CTOR_IMP(VvMajority) {
    VvMajority__Syms* __restrict vlSymsp = __VlSymsp = new VvMajority__Syms(this, name());
    VvMajority* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Reset internal values
    
    // Reset structure values
    _ctor_var_reset();
}

void VvMajority::__Vconfigure(VvMajority__Syms* vlSymsp, bool first) {
    if (false && first) {}  // Prevent unused
    this->__VlSymsp = vlSymsp;
    if (false && this->__VlSymsp) {}  // Prevent unused
    Verilated::timeunit(-12);
    Verilated::timeprecision(-12);
}

VvMajority::~VvMajority() {
    VL_DO_CLEAR(delete __VlSymsp, __VlSymsp = NULL);
}

void VvMajority::_eval_initial(VvMajority__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvMajority::_eval_initial\n"); );
    VvMajority* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
}

void VvMajority::final() {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvMajority::final\n"); );
    // Variables
    VvMajority__Syms* __restrict vlSymsp = this->__VlSymsp;
    VvMajority* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
}

void VvMajority::_eval_settle(VvMajority__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvMajority::_eval_settle\n"); );
    VvMajority* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    vlTOPp->_combo__TOP__1(vlSymsp);
}

void VvMajority::_ctor_var_reset() {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvMajority::_ctor_var_reset\n"); );
    // Body
    a = VL_RAND_RESET_I(7);
    m = VL_RAND_RESET_I(1);
}
