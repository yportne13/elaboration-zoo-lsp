// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See VvUintToOhM1.h for the primary calling header

#include "VvUintToOhM1.h"
#include "VvUintToOhM1__Syms.h"

//==========

VL_CTOR_IMP(VvUintToOhM1) {
    VvUintToOhM1__Syms* __restrict vlSymsp = __VlSymsp = new VvUintToOhM1__Syms(this, name());
    VvUintToOhM1* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Reset internal values
    
    // Reset structure values
    _ctor_var_reset();
}

void VvUintToOhM1::__Vconfigure(VvUintToOhM1__Syms* vlSymsp, bool first) {
    if (false && first) {}  // Prevent unused
    this->__VlSymsp = vlSymsp;
    if (false && this->__VlSymsp) {}  // Prevent unused
    Verilated::timeunit(-12);
    Verilated::timeprecision(-12);
}

VvUintToOhM1::~VvUintToOhM1() {
    VL_DO_CLEAR(delete __VlSymsp, __VlSymsp = NULL);
}

void VvUintToOhM1::_eval_initial(VvUintToOhM1__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvUintToOhM1::_eval_initial\n"); );
    VvUintToOhM1* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
}

void VvUintToOhM1::final() {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvUintToOhM1::final\n"); );
    // Variables
    VvUintToOhM1__Syms* __restrict vlSymsp = this->__VlSymsp;
    VvUintToOhM1* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
}

void VvUintToOhM1::_eval_settle(VvUintToOhM1__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvUintToOhM1::_eval_settle\n"); );
    VvUintToOhM1* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    vlTOPp->_combo__TOP__1(vlSymsp);
}

void VvUintToOhM1::_ctor_var_reset() {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvUintToOhM1::_ctor_var_reset\n"); );
    // Body
    a = VL_RAND_RESET_I(3);
    oh = VL_RAND_RESET_I(8);
}
