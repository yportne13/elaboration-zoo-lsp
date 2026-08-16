// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See VvCountOneU.h for the primary calling header

#include "VvCountOneU.h"
#include "VvCountOneU__Syms.h"

//==========

VL_CTOR_IMP(VvCountOneU) {
    VvCountOneU__Syms* __restrict vlSymsp = __VlSymsp = new VvCountOneU__Syms(this, name());
    VvCountOneU* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Reset internal values
    
    // Reset structure values
    _ctor_var_reset();
}

void VvCountOneU::__Vconfigure(VvCountOneU__Syms* vlSymsp, bool first) {
    if (false && first) {}  // Prevent unused
    this->__VlSymsp = vlSymsp;
    if (false && this->__VlSymsp) {}  // Prevent unused
    Verilated::timeunit(-12);
    Verilated::timeprecision(-12);
}

VvCountOneU::~VvCountOneU() {
    VL_DO_CLEAR(delete __VlSymsp, __VlSymsp = NULL);
}

void VvCountOneU::_eval_initial(VvCountOneU__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvCountOneU::_eval_initial\n"); );
    VvCountOneU* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
}

void VvCountOneU::final() {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvCountOneU::final\n"); );
    // Variables
    VvCountOneU__Syms* __restrict vlSymsp = this->__VlSymsp;
    VvCountOneU* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
}

void VvCountOneU::_eval_settle(VvCountOneU__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvCountOneU::_eval_settle\n"); );
    VvCountOneU* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    vlTOPp->_combo__TOP__1(vlSymsp);
}

void VvCountOneU::_ctor_var_reset() {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvCountOneU::_ctor_var_reset\n"); );
    // Body
    a = VL_RAND_RESET_I(8);
    c = VL_RAND_RESET_I(4);
}
