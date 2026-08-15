// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See VvStreamMux.h for the primary calling header

#include "VvStreamMux.h"
#include "VvStreamMux__Syms.h"

//==========

VL_CTOR_IMP(VvStreamMux) {
    VvStreamMux__Syms* __restrict vlSymsp = __VlSymsp = new VvStreamMux__Syms(this, name());
    VvStreamMux* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Reset internal values
    
    // Reset structure values
    _ctor_var_reset();
}

void VvStreamMux::__Vconfigure(VvStreamMux__Syms* vlSymsp, bool first) {
    if (false && first) {}  // Prevent unused
    this->__VlSymsp = vlSymsp;
    if (false && this->__VlSymsp) {}  // Prevent unused
    Verilated::timeunit(-12);
    Verilated::timeprecision(-12);
}

VvStreamMux::~VvStreamMux() {
    VL_DO_CLEAR(delete __VlSymsp, __VlSymsp = NULL);
}

void VvStreamMux::_eval_initial(VvStreamMux__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvStreamMux::_eval_initial\n"); );
    VvStreamMux* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
}

void VvStreamMux::final() {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvStreamMux::final\n"); );
    // Variables
    VvStreamMux__Syms* __restrict vlSymsp = this->__VlSymsp;
    VvStreamMux* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
}

void VvStreamMux::_eval_settle(VvStreamMux__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvStreamMux::_eval_settle\n"); );
    VvStreamMux* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    vlTOPp->_combo__TOP__1(vlSymsp);
}

void VvStreamMux::_ctor_var_reset() {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvStreamMux::_ctor_var_reset\n"); );
    // Body
    sel = VL_RAND_RESET_I(1);
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
