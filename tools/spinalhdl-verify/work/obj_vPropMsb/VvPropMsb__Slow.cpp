// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See VvPropMsb.h for the primary calling header

#include "VvPropMsb.h"
#include "VvPropMsb__Syms.h"

//==========

VL_CTOR_IMP(VvPropMsb) {
    VvPropMsb__Syms* __restrict vlSymsp = __VlSymsp = new VvPropMsb__Syms(this, name());
    VvPropMsb* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Reset internal values
    
    // Reset structure values
    _ctor_var_reset();
}

void VvPropMsb::__Vconfigure(VvPropMsb__Syms* vlSymsp, bool first) {
    if (false && first) {}  // Prevent unused
    this->__VlSymsp = vlSymsp;
    if (false && this->__VlSymsp) {}  // Prevent unused
    Verilated::timeunit(-12);
    Verilated::timeprecision(-12);
}

VvPropMsb::~VvPropMsb() {
    VL_DO_CLEAR(delete __VlSymsp, __VlSymsp = NULL);
}

void VvPropMsb::_eval_initial(VvPropMsb__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvPropMsb::_eval_initial\n"); );
    VvPropMsb* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
}

void VvPropMsb::final() {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvPropMsb::final\n"); );
    // Variables
    VvPropMsb__Syms* __restrict vlSymsp = this->__VlSymsp;
    VvPropMsb* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
}

void VvPropMsb::_eval_settle(VvPropMsb__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvPropMsb::_eval_settle\n"); );
    VvPropMsb* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    vlTOPp->_combo__TOP__1(vlSymsp);
}

void VvPropMsb::_ctor_var_reset() {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvPropMsb::_ctor_var_reset\n"); );
    // Body
    a = VL_RAND_RESET_I(8);
    r = VL_RAND_RESET_I(8);
}
