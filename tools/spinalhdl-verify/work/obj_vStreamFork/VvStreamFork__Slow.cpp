// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See VvStreamFork.h for the primary calling header

#include "VvStreamFork.h"
#include "VvStreamFork__Syms.h"

//==========

VL_CTOR_IMP(VvStreamFork) {
    VvStreamFork__Syms* __restrict vlSymsp = __VlSymsp = new VvStreamFork__Syms(this, name());
    VvStreamFork* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Reset internal values
    
    // Reset structure values
    _ctor_var_reset();
}

void VvStreamFork::__Vconfigure(VvStreamFork__Syms* vlSymsp, bool first) {
    if (false && first) {}  // Prevent unused
    this->__VlSymsp = vlSymsp;
    if (false && this->__VlSymsp) {}  // Prevent unused
    Verilated::timeunit(-12);
    Verilated::timeprecision(-12);
}

VvStreamFork::~VvStreamFork() {
    VL_DO_CLEAR(delete __VlSymsp, __VlSymsp = NULL);
}

void VvStreamFork::_eval_initial(VvStreamFork__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvStreamFork::_eval_initial\n"); );
    VvStreamFork* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
}

void VvStreamFork::final() {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvStreamFork::final\n"); );
    // Variables
    VvStreamFork__Syms* __restrict vlSymsp = this->__VlSymsp;
    VvStreamFork* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
}

void VvStreamFork::_eval_settle(VvStreamFork__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvStreamFork::_eval_settle\n"); );
    VvStreamFork* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    vlTOPp->_combo__TOP__1(vlSymsp);
}

void VvStreamFork::_ctor_var_reset() {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvStreamFork::_ctor_var_reset\n"); );
    // Body
    in_valid = VL_RAND_RESET_I(1);
    in_payload = VL_RAND_RESET_I(8);
    in_ready = VL_RAND_RESET_I(1);
    o0_valid = VL_RAND_RESET_I(1);
    o0_ready = VL_RAND_RESET_I(1);
    o0_payload = VL_RAND_RESET_I(8);
    o1_valid = VL_RAND_RESET_I(1);
    o1_ready = VL_RAND_RESET_I(1);
    o1_payload = VL_RAND_RESET_I(8);
}
