// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See VvLog2Ceil.h for the primary calling header

#include "VvLog2Ceil.h"
#include "VvLog2Ceil__Syms.h"

//==========

VL_CTOR_IMP(VvLog2Ceil) {
    VvLog2Ceil__Syms* __restrict vlSymsp = __VlSymsp = new VvLog2Ceil__Syms(this, name());
    VvLog2Ceil* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Reset internal values
    
    // Reset structure values
    _ctor_var_reset();
}

void VvLog2Ceil::__Vconfigure(VvLog2Ceil__Syms* vlSymsp, bool first) {
    if (false && first) {}  // Prevent unused
    this->__VlSymsp = vlSymsp;
    if (false && this->__VlSymsp) {}  // Prevent unused
    Verilated::timeunit(-12);
    Verilated::timeprecision(-12);
}

VvLog2Ceil::~VvLog2Ceil() {
    VL_DO_CLEAR(delete __VlSymsp, __VlSymsp = NULL);
}

void VvLog2Ceil::_eval_initial(VvLog2Ceil__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvLog2Ceil::_eval_initial\n"); );
    VvLog2Ceil* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
}

void VvLog2Ceil::final() {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvLog2Ceil::final\n"); );
    // Variables
    VvLog2Ceil__Syms* __restrict vlSymsp = this->__VlSymsp;
    VvLog2Ceil* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
}

void VvLog2Ceil::_eval_settle(VvLog2Ceil__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvLog2Ceil::_eval_settle\n"); );
    VvLog2Ceil* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    vlTOPp->_combo__TOP__1(vlSymsp);
}

void VvLog2Ceil::_ctor_var_reset() {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvLog2Ceil::_ctor_var_reset\n"); );
    // Body
    a = VL_RAND_RESET_I(8);
    lc = VL_RAND_RESET_I(4);
}
