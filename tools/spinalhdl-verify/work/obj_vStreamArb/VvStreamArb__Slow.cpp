// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See VvStreamArb.h for the primary calling header

#include "VvStreamArb.h"
#include "VvStreamArb__Syms.h"

//==========

VL_CTOR_IMP(VvStreamArb) {
    VvStreamArb__Syms* __restrict vlSymsp = __VlSymsp = new VvStreamArb__Syms(this, name());
    VvStreamArb* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Reset internal values
    
    // Reset structure values
    _ctor_var_reset();
}

void VvStreamArb::__Vconfigure(VvStreamArb__Syms* vlSymsp, bool first) {
    if (false && first) {}  // Prevent unused
    this->__VlSymsp = vlSymsp;
    if (false && this->__VlSymsp) {}  // Prevent unused
    Verilated::timeunit(-12);
    Verilated::timeprecision(-12);
}

VvStreamArb::~VvStreamArb() {
    VL_DO_CLEAR(delete __VlSymsp, __VlSymsp = NULL);
}

void VvStreamArb::_eval_initial(VvStreamArb__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvStreamArb::_eval_initial\n"); );
    VvStreamArb* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
}

void VvStreamArb::final() {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvStreamArb::final\n"); );
    // Variables
    VvStreamArb__Syms* __restrict vlSymsp = this->__VlSymsp;
    VvStreamArb* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
}

void VvStreamArb::_eval_settle(VvStreamArb__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvStreamArb::_eval_settle\n"); );
    VvStreamArb* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    vlTOPp->_combo__TOP__1(vlSymsp);
}

void VvStreamArb::_ctor_var_reset() {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvStreamArb::_ctor_var_reset\n"); );
    // Body
    a_valid = VL_RAND_RESET_I(1);
    a_payload = VL_RAND_RESET_I(8);
    a_ready = VL_RAND_RESET_I(1);
    b_valid = VL_RAND_RESET_I(1);
    b_payload = VL_RAND_RESET_I(8);
    b_ready = VL_RAND_RESET_I(1);
    m_valid = VL_RAND_RESET_I(1);
    m_ready = VL_RAND_RESET_I(1);
    m_payload = VL_RAND_RESET_I(8);
}
