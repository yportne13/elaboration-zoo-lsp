// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See VvReverseU.h for the primary calling header

#include "VvReverseU.h"
#include "VvReverseU__Syms.h"

//==========

VL_CTOR_IMP(VvReverseU) {
    VvReverseU__Syms* __restrict vlSymsp = __VlSymsp = new VvReverseU__Syms(this, name());
    VvReverseU* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Reset internal values
    
    // Reset structure values
    _ctor_var_reset();
}

void VvReverseU::__Vconfigure(VvReverseU__Syms* vlSymsp, bool first) {
    if (false && first) {}  // Prevent unused
    this->__VlSymsp = vlSymsp;
    if (false && this->__VlSymsp) {}  // Prevent unused
    Verilated::timeunit(-12);
    Verilated::timeprecision(-12);
}

VvReverseU::~VvReverseU() {
    VL_DO_CLEAR(delete __VlSymsp, __VlSymsp = NULL);
}

void VvReverseU::_eval_initial(VvReverseU__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvReverseU::_eval_initial\n"); );
    VvReverseU* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
}

void VvReverseU::final() {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvReverseU::final\n"); );
    // Variables
    VvReverseU__Syms* __restrict vlSymsp = this->__VlSymsp;
    VvReverseU* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
}

void VvReverseU::_eval_settle(VvReverseU__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvReverseU::_eval_settle\n"); );
    VvReverseU* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    vlTOPp->_combo__TOP__1(vlSymsp);
}

void VvReverseU::_ctor_var_reset() {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvReverseU::_ctor_var_reset\n"); );
    // Body
    a = VL_RAND_RESET_I(8);
    r = VL_RAND_RESET_I(8);
}
