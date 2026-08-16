// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See VvUintToOh.h for the primary calling header

#include "VvUintToOh.h"
#include "VvUintToOh__Syms.h"

//==========

VL_CTOR_IMP(VvUintToOh) {
    VvUintToOh__Syms* __restrict vlSymsp = __VlSymsp = new VvUintToOh__Syms(this, name());
    VvUintToOh* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Reset internal values
    
    // Reset structure values
    _ctor_var_reset();
}

void VvUintToOh::__Vconfigure(VvUintToOh__Syms* vlSymsp, bool first) {
    if (false && first) {}  // Prevent unused
    this->__VlSymsp = vlSymsp;
    if (false && this->__VlSymsp) {}  // Prevent unused
    Verilated::timeunit(-12);
    Verilated::timeprecision(-12);
}

VvUintToOh::~VvUintToOh() {
    VL_DO_CLEAR(delete __VlSymsp, __VlSymsp = NULL);
}

void VvUintToOh::_eval_initial(VvUintToOh__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvUintToOh::_eval_initial\n"); );
    VvUintToOh* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
}

void VvUintToOh::final() {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvUintToOh::final\n"); );
    // Variables
    VvUintToOh__Syms* __restrict vlSymsp = this->__VlSymsp;
    VvUintToOh* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
}

void VvUintToOh::_eval_settle(VvUintToOh__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvUintToOh::_eval_settle\n"); );
    VvUintToOh* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    vlTOPp->_combo__TOP__1(vlSymsp);
}

void VvUintToOh::_ctor_var_reset() {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvUintToOh::_ctor_var_reset\n"); );
    // Body
    a = VL_RAND_RESET_I(3);
    oh = VL_RAND_RESET_I(8);
}
