// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See VvLog2Floor.h for the primary calling header

#include "VvLog2Floor.h"
#include "VvLog2Floor__Syms.h"

//==========

VL_CTOR_IMP(VvLog2Floor) {
    VvLog2Floor__Syms* __restrict vlSymsp = __VlSymsp = new VvLog2Floor__Syms(this, name());
    VvLog2Floor* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Reset internal values
    
    // Reset structure values
    _ctor_var_reset();
}

void VvLog2Floor::__Vconfigure(VvLog2Floor__Syms* vlSymsp, bool first) {
    if (false && first) {}  // Prevent unused
    this->__VlSymsp = vlSymsp;
    if (false && this->__VlSymsp) {}  // Prevent unused
    Verilated::timeunit(-12);
    Verilated::timeprecision(-12);
}

VvLog2Floor::~VvLog2Floor() {
    VL_DO_CLEAR(delete __VlSymsp, __VlSymsp = NULL);
}

void VvLog2Floor::_eval_initial(VvLog2Floor__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvLog2Floor::_eval_initial\n"); );
    VvLog2Floor* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
}

void VvLog2Floor::final() {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvLog2Floor::final\n"); );
    // Variables
    VvLog2Floor__Syms* __restrict vlSymsp = this->__VlSymsp;
    VvLog2Floor* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
}

void VvLog2Floor::_eval_settle(VvLog2Floor__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvLog2Floor::_eval_settle\n"); );
    VvLog2Floor* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    vlTOPp->_combo__TOP__1(vlSymsp);
}

void VvLog2Floor::_ctor_var_reset() {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvLog2Floor::_ctor_var_reset\n"); );
    // Body
    a = VL_RAND_RESET_I(8);
    lf = VL_RAND_RESET_I(3);
}
