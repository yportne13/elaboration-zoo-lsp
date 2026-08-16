// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See VvNapot.h for the primary calling header

#include "VvNapot.h"
#include "VvNapot__Syms.h"

//==========

VL_CTOR_IMP(VvNapot) {
    VvNapot__Syms* __restrict vlSymsp = __VlSymsp = new VvNapot__Syms(this, name());
    VvNapot* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Reset internal values
    
    // Reset structure values
    _ctor_var_reset();
}

void VvNapot::__Vconfigure(VvNapot__Syms* vlSymsp, bool first) {
    if (false && first) {}  // Prevent unused
    this->__VlSymsp = vlSymsp;
    if (false && this->__VlSymsp) {}  // Prevent unused
    Verilated::timeunit(-12);
    Verilated::timeprecision(-12);
}

VvNapot::~VvNapot() {
    VL_DO_CLEAR(delete __VlSymsp, __VlSymsp = NULL);
}

void VvNapot::_eval_initial(VvNapot__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvNapot::_eval_initial\n"); );
    VvNapot* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
}

void VvNapot::final() {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvNapot::final\n"); );
    // Variables
    VvNapot__Syms* __restrict vlSymsp = this->__VlSymsp;
    VvNapot* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
}

void VvNapot::_eval_settle(VvNapot__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvNapot::_eval_settle\n"); );
    VvNapot* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    vlTOPp->_combo__TOP__1(vlSymsp);
}

void VvNapot::_ctor_var_reset() {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvNapot::_ctor_var_reset\n"); );
    // Body
    a = VL_RAND_RESET_I(4);
    n = VL_RAND_RESET_I(5);
}
