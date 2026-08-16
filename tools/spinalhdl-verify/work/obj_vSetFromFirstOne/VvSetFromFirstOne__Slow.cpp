// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See VvSetFromFirstOne.h for the primary calling header

#include "VvSetFromFirstOne.h"
#include "VvSetFromFirstOne__Syms.h"

//==========

VL_CTOR_IMP(VvSetFromFirstOne) {
    VvSetFromFirstOne__Syms* __restrict vlSymsp = __VlSymsp = new VvSetFromFirstOne__Syms(this, name());
    VvSetFromFirstOne* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Reset internal values
    
    // Reset structure values
    _ctor_var_reset();
}

void VvSetFromFirstOne::__Vconfigure(VvSetFromFirstOne__Syms* vlSymsp, bool first) {
    if (false && first) {}  // Prevent unused
    this->__VlSymsp = vlSymsp;
    if (false && this->__VlSymsp) {}  // Prevent unused
    Verilated::timeunit(-12);
    Verilated::timeprecision(-12);
}

VvSetFromFirstOne::~VvSetFromFirstOne() {
    VL_DO_CLEAR(delete __VlSymsp, __VlSymsp = NULL);
}

void VvSetFromFirstOne::_eval_initial(VvSetFromFirstOne__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvSetFromFirstOne::_eval_initial\n"); );
    VvSetFromFirstOne* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
}

void VvSetFromFirstOne::final() {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvSetFromFirstOne::final\n"); );
    // Variables
    VvSetFromFirstOne__Syms* __restrict vlSymsp = this->__VlSymsp;
    VvSetFromFirstOne* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
}

void VvSetFromFirstOne::_eval_settle(VvSetFromFirstOne__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvSetFromFirstOne::_eval_settle\n"); );
    VvSetFromFirstOne* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    vlTOPp->_combo__TOP__1(vlSymsp);
}

void VvSetFromFirstOne::_ctor_var_reset() {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvSetFromFirstOne::_ctor_var_reset\n"); );
    // Body
    a = VL_RAND_RESET_I(8);
    s = VL_RAND_RESET_I(8);
}
