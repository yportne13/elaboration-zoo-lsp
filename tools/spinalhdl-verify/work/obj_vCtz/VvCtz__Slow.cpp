// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See VvCtz.h for the primary calling header

#include "VvCtz.h"
#include "VvCtz__Syms.h"

//==========

VL_CTOR_IMP(VvCtz) {
    VvCtz__Syms* __restrict vlSymsp = __VlSymsp = new VvCtz__Syms(this, name());
    VvCtz* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Reset internal values
    
    // Reset structure values
    _ctor_var_reset();
}

void VvCtz::__Vconfigure(VvCtz__Syms* vlSymsp, bool first) {
    if (false && first) {}  // Prevent unused
    this->__VlSymsp = vlSymsp;
    if (false && this->__VlSymsp) {}  // Prevent unused
    Verilated::timeunit(-12);
    Verilated::timeprecision(-12);
}

VvCtz::~VvCtz() {
    VL_DO_CLEAR(delete __VlSymsp, __VlSymsp = NULL);
}

void VvCtz::_eval_initial(VvCtz__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvCtz::_eval_initial\n"); );
    VvCtz* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
}

void VvCtz::final() {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvCtz::final\n"); );
    // Variables
    VvCtz__Syms* __restrict vlSymsp = this->__VlSymsp;
    VvCtz* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
}

void VvCtz::_eval_settle(VvCtz__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvCtz::_eval_settle\n"); );
    VvCtz* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    vlTOPp->_combo__TOP__1(vlSymsp);
}

void VvCtz::_ctor_var_reset() {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvCtz::_ctor_var_reset\n"); );
    // Body
    a = VL_RAND_RESET_I(8);
    c = VL_RAND_RESET_I(4);
}
