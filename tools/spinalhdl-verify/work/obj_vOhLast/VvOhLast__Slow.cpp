// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See VvOhLast.h for the primary calling header

#include "VvOhLast.h"
#include "VvOhLast__Syms.h"

//==========

VL_CTOR_IMP(VvOhLast) {
    VvOhLast__Syms* __restrict vlSymsp = __VlSymsp = new VvOhLast__Syms(this, name());
    VvOhLast* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Reset internal values
    
    // Reset structure values
    _ctor_var_reset();
}

void VvOhLast::__Vconfigure(VvOhLast__Syms* vlSymsp, bool first) {
    if (false && first) {}  // Prevent unused
    this->__VlSymsp = vlSymsp;
    if (false && this->__VlSymsp) {}  // Prevent unused
    Verilated::timeunit(-12);
    Verilated::timeprecision(-12);
}

VvOhLast::~VvOhLast() {
    VL_DO_CLEAR(delete __VlSymsp, __VlSymsp = NULL);
}

void VvOhLast::_eval_initial(VvOhLast__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvOhLast::_eval_initial\n"); );
    VvOhLast* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
}

void VvOhLast::final() {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvOhLast::final\n"); );
    // Variables
    VvOhLast__Syms* __restrict vlSymsp = this->__VlSymsp;
    VvOhLast* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
}

void VvOhLast::_eval_settle(VvOhLast__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvOhLast::_eval_settle\n"); );
    VvOhLast* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    vlTOPp->_combo__TOP__1(vlSymsp);
}

void VvOhLast::_ctor_var_reset() {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvOhLast::_ctor_var_reset\n"); );
    // Body
    oh = VL_RAND_RESET_I(8);
    l = VL_RAND_RESET_I(8);
}
