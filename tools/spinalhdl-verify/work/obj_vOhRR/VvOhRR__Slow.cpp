// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See VvOhRR.h for the primary calling header

#include "VvOhRR.h"
#include "VvOhRR__Syms.h"

//==========

VL_CTOR_IMP(VvOhRR) {
    VvOhRR__Syms* __restrict vlSymsp = __VlSymsp = new VvOhRR__Syms(this, name());
    VvOhRR* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Reset internal values
    
    // Reset structure values
    _ctor_var_reset();
}

void VvOhRR::__Vconfigure(VvOhRR__Syms* vlSymsp, bool first) {
    if (false && first) {}  // Prevent unused
    this->__VlSymsp = vlSymsp;
    if (false && this->__VlSymsp) {}  // Prevent unused
    Verilated::timeunit(-12);
    Verilated::timeprecision(-12);
}

VvOhRR::~VvOhRR() {
    VL_DO_CLEAR(delete __VlSymsp, __VlSymsp = NULL);
}

void VvOhRR::_eval_initial(VvOhRR__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvOhRR::_eval_initial\n"); );
    VvOhRR* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
}

void VvOhRR::final() {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvOhRR::final\n"); );
    // Variables
    VvOhRR__Syms* __restrict vlSymsp = this->__VlSymsp;
    VvOhRR* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
}

void VvOhRR::_eval_settle(VvOhRR__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvOhRR::_eval_settle\n"); );
    VvOhRR* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    vlTOPp->_combo__TOP__1(vlSymsp);
}

void VvOhRR::_ctor_var_reset() {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvOhRR::_ctor_var_reset\n"); );
    // Body
    req = VL_RAND_RESET_I(4);
    pri = VL_RAND_RESET_I(4);
    g = VL_RAND_RESET_I(4);
}
