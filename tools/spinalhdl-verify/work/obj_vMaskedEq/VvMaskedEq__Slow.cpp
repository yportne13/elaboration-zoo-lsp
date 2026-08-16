// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See VvMaskedEq.h for the primary calling header

#include "VvMaskedEq.h"
#include "VvMaskedEq__Syms.h"

//==========

VL_CTOR_IMP(VvMaskedEq) {
    VvMaskedEq__Syms* __restrict vlSymsp = __VlSymsp = new VvMaskedEq__Syms(this, name());
    VvMaskedEq* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Reset internal values
    
    // Reset structure values
    _ctor_var_reset();
}

void VvMaskedEq::__Vconfigure(VvMaskedEq__Syms* vlSymsp, bool first) {
    if (false && first) {}  // Prevent unused
    this->__VlSymsp = vlSymsp;
    if (false && this->__VlSymsp) {}  // Prevent unused
    Verilated::timeunit(-12);
    Verilated::timeprecision(-12);
}

VvMaskedEq::~VvMaskedEq() {
    VL_DO_CLEAR(delete __VlSymsp, __VlSymsp = NULL);
}

void VvMaskedEq::_eval_initial(VvMaskedEq__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvMaskedEq::_eval_initial\n"); );
    VvMaskedEq* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
}

void VvMaskedEq::final() {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvMaskedEq::final\n"); );
    // Variables
    VvMaskedEq__Syms* __restrict vlSymsp = this->__VlSymsp;
    VvMaskedEq* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
}

void VvMaskedEq::_eval_settle(VvMaskedEq__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvMaskedEq::_eval_settle\n"); );
    VvMaskedEq* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    vlTOPp->_combo__TOP__1(vlSymsp);
}

void VvMaskedEq::_ctor_var_reset() {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvMaskedEq::_ctor_var_reset\n"); );
    // Body
    hard = VL_RAND_RESET_I(4);
    eq = VL_RAND_RESET_I(1);
}
