// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See VvClz.h for the primary calling header

#include "VvClz.h"
#include "VvClz__Syms.h"

//==========

VL_CTOR_IMP(VvClz) {
    VvClz__Syms* __restrict vlSymsp = __VlSymsp = new VvClz__Syms(this, name());
    VvClz* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Reset internal values
    
    // Reset structure values
    _ctor_var_reset();
}

void VvClz::__Vconfigure(VvClz__Syms* vlSymsp, bool first) {
    if (false && first) {}  // Prevent unused
    this->__VlSymsp = vlSymsp;
    if (false && this->__VlSymsp) {}  // Prevent unused
    Verilated::timeunit(-12);
    Verilated::timeprecision(-12);
}

VvClz::~VvClz() {
    VL_DO_CLEAR(delete __VlSymsp, __VlSymsp = NULL);
}

void VvClz::_eval_initial(VvClz__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvClz::_eval_initial\n"); );
    VvClz* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
}

void VvClz::final() {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvClz::final\n"); );
    // Variables
    VvClz__Syms* __restrict vlSymsp = this->__VlSymsp;
    VvClz* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
}

void VvClz::_eval_settle(VvClz__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvClz::_eval_settle\n"); );
    VvClz* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    vlTOPp->_combo__TOP__1(vlSymsp);
}

void VvClz::_ctor_var_reset() {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvClz::_ctor_var_reset\n"); );
    // Body
    a = VL_RAND_RESET_I(8);
    c = VL_RAND_RESET_I(4);
}
