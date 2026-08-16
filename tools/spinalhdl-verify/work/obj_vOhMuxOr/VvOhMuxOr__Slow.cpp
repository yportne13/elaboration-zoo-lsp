// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See VvOhMuxOr.h for the primary calling header

#include "VvOhMuxOr.h"
#include "VvOhMuxOr__Syms.h"

//==========

VL_CTOR_IMP(VvOhMuxOr) {
    VvOhMuxOr__Syms* __restrict vlSymsp = __VlSymsp = new VvOhMuxOr__Syms(this, name());
    VvOhMuxOr* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Reset internal values
    
    // Reset structure values
    _ctor_var_reset();
}

void VvOhMuxOr::__Vconfigure(VvOhMuxOr__Syms* vlSymsp, bool first) {
    if (false && first) {}  // Prevent unused
    this->__VlSymsp = vlSymsp;
    if (false && this->__VlSymsp) {}  // Prevent unused
    Verilated::timeunit(-12);
    Verilated::timeprecision(-12);
}

VvOhMuxOr::~VvOhMuxOr() {
    VL_DO_CLEAR(delete __VlSymsp, __VlSymsp = NULL);
}

void VvOhMuxOr::_eval_initial(VvOhMuxOr__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvOhMuxOr::_eval_initial\n"); );
    VvOhMuxOr* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
}

void VvOhMuxOr::final() {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvOhMuxOr::final\n"); );
    // Variables
    VvOhMuxOr__Syms* __restrict vlSymsp = this->__VlSymsp;
    VvOhMuxOr* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
}

void VvOhMuxOr::_eval_settle(VvOhMuxOr__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvOhMuxOr::_eval_settle\n"); );
    VvOhMuxOr* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    vlTOPp->_combo__TOP__1(vlSymsp);
}

void VvOhMuxOr::_ctor_var_reset() {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvOhMuxOr::_ctor_var_reset\n"); );
    // Body
    sel = VL_RAND_RESET_I(4);
    a = VL_RAND_RESET_I(8);
    b = VL_RAND_RESET_I(8);
    c = VL_RAND_RESET_I(8);
    d = VL_RAND_RESET_I(8);
    o = VL_RAND_RESET_I(8);
}
