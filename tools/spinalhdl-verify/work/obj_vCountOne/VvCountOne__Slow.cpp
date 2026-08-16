// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See VvCountOne.h for the primary calling header

#include "VvCountOne.h"
#include "VvCountOne__Syms.h"

//==========

VL_CTOR_IMP(VvCountOne) {
    VvCountOne__Syms* __restrict vlSymsp = __VlSymsp = new VvCountOne__Syms(this, name());
    VvCountOne* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Reset internal values
    
    // Reset structure values
    _ctor_var_reset();
}

void VvCountOne::__Vconfigure(VvCountOne__Syms* vlSymsp, bool first) {
    if (false && first) {}  // Prevent unused
    this->__VlSymsp = vlSymsp;
    if (false && this->__VlSymsp) {}  // Prevent unused
    Verilated::timeunit(-12);
    Verilated::timeprecision(-12);
}

VvCountOne::~VvCountOne() {
    VL_DO_CLEAR(delete __VlSymsp, __VlSymsp = NULL);
}

void VvCountOne::_eval_initial(VvCountOne__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvCountOne::_eval_initial\n"); );
    VvCountOne* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
}

void VvCountOne::final() {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvCountOne::final\n"); );
    // Variables
    VvCountOne__Syms* __restrict vlSymsp = this->__VlSymsp;
    VvCountOne* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
}

void VvCountOne::_eval_settle(VvCountOne__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvCountOne::_eval_settle\n"); );
    VvCountOne* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    vlTOPp->_combo__TOP__1(vlSymsp);
}

void VvCountOne::_ctor_var_reset() {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvCountOne::_ctor_var_reset\n"); );
    // Body
    a = VL_RAND_RESET_I(8);
    c = VL_RAND_RESET_I(4);
}
