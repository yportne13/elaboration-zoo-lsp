// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See VvAddCarry.h for the primary calling header

#include "VvAddCarry.h"
#include "VvAddCarry__Syms.h"

//==========

VL_CTOR_IMP(VvAddCarry) {
    VvAddCarry__Syms* __restrict vlSymsp = __VlSymsp = new VvAddCarry__Syms(this, name());
    VvAddCarry* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Reset internal values
    
    // Reset structure values
    _ctor_var_reset();
}

void VvAddCarry::__Vconfigure(VvAddCarry__Syms* vlSymsp, bool first) {
    if (false && first) {}  // Prevent unused
    this->__VlSymsp = vlSymsp;
    if (false && this->__VlSymsp) {}  // Prevent unused
    Verilated::timeunit(-12);
    Verilated::timeprecision(-12);
}

VvAddCarry::~VvAddCarry() {
    VL_DO_CLEAR(delete __VlSymsp, __VlSymsp = NULL);
}

void VvAddCarry::_eval_initial(VvAddCarry__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvAddCarry::_eval_initial\n"); );
    VvAddCarry* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
}

void VvAddCarry::final() {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvAddCarry::final\n"); );
    // Variables
    VvAddCarry__Syms* __restrict vlSymsp = this->__VlSymsp;
    VvAddCarry* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
}

void VvAddCarry::_eval_settle(VvAddCarry__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvAddCarry::_eval_settle\n"); );
    VvAddCarry* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    vlTOPp->_combo__TOP__1(vlSymsp);
}

void VvAddCarry::_ctor_var_reset() {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvAddCarry::_ctor_var_reset\n"); );
    // Body
    a = VL_RAND_RESET_I(8);
    b = VL_RAND_RESET_I(8);
    sum = VL_RAND_RESET_I(8);
    carry = VL_RAND_RESET_I(1);
}
