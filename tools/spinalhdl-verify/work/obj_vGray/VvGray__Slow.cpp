// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See VvGray.h for the primary calling header

#include "VvGray.h"
#include "VvGray__Syms.h"

//==========

VL_CTOR_IMP(VvGray) {
    VvGray__Syms* __restrict vlSymsp = __VlSymsp = new VvGray__Syms(this, name());
    VvGray* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Reset internal values
    
    // Reset structure values
    _ctor_var_reset();
}

void VvGray::__Vconfigure(VvGray__Syms* vlSymsp, bool first) {
    if (false && first) {}  // Prevent unused
    this->__VlSymsp = vlSymsp;
    if (false && this->__VlSymsp) {}  // Prevent unused
    Verilated::timeunit(-12);
    Verilated::timeprecision(-12);
}

VvGray::~VvGray() {
    VL_DO_CLEAR(delete __VlSymsp, __VlSymsp = NULL);
}

void VvGray::_eval_initial(VvGray__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvGray::_eval_initial\n"); );
    VvGray* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
}

void VvGray::final() {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvGray::final\n"); );
    // Variables
    VvGray__Syms* __restrict vlSymsp = this->__VlSymsp;
    VvGray* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
}

void VvGray::_eval_settle(VvGray__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvGray::_eval_settle\n"); );
    VvGray* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    vlTOPp->_combo__TOP__1(vlSymsp);
}

void VvGray::_ctor_var_reset() {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvGray::_ctor_var_reset\n"); );
    // Body
    x = VL_RAND_RESET_I(8);
    g = VL_RAND_RESET_I(8);
    back = VL_RAND_RESET_I(8);
}
