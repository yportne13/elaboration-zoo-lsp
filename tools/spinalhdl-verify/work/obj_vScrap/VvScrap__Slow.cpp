// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See VvScrap.h for the primary calling header

#include "VvScrap.h"
#include "VvScrap__Syms.h"

//==========

VL_CTOR_IMP(VvScrap) {
    VvScrap__Syms* __restrict vlSymsp = __VlSymsp = new VvScrap__Syms(this, name());
    VvScrap* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Reset internal values
    
    // Reset structure values
    _ctor_var_reset();
}

void VvScrap::__Vconfigure(VvScrap__Syms* vlSymsp, bool first) {
    if (false && first) {}  // Prevent unused
    this->__VlSymsp = vlSymsp;
    if (false && this->__VlSymsp) {}  // Prevent unused
    Verilated::timeunit(-12);
    Verilated::timeprecision(-12);
}

VvScrap::~VvScrap() {
    VL_DO_CLEAR(delete __VlSymsp, __VlSymsp = NULL);
}

void VvScrap::_eval_initial(VvScrap__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvScrap::_eval_initial\n"); );
    VvScrap* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
}

void VvScrap::final() {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvScrap::final\n"); );
    // Variables
    VvScrap__Syms* __restrict vlSymsp = this->__VlSymsp;
    VvScrap* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
}

void VvScrap::_eval_settle(VvScrap__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvScrap::_eval_settle\n"); );
    VvScrap* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    vlTOPp->_combo__TOP__1(vlSymsp);
}

void VvScrap::_ctor_var_reset() {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvScrap::_ctor_var_reset\n"); );
    // Body
    a = VL_RAND_RESET_I(8);
    sh = VL_RAND_RESET_I(3);
    s = VL_RAND_RESET_I(8);
}
