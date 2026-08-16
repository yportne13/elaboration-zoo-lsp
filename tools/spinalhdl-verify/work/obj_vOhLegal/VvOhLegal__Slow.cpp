// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See VvOhLegal.h for the primary calling header

#include "VvOhLegal.h"
#include "VvOhLegal__Syms.h"

//==========

VL_CTOR_IMP(VvOhLegal) {
    VvOhLegal__Syms* __restrict vlSymsp = __VlSymsp = new VvOhLegal__Syms(this, name());
    VvOhLegal* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Reset internal values
    
    // Reset structure values
    _ctor_var_reset();
}

void VvOhLegal::__Vconfigure(VvOhLegal__Syms* vlSymsp, bool first) {
    if (false && first) {}  // Prevent unused
    this->__VlSymsp = vlSymsp;
    if (false && this->__VlSymsp) {}  // Prevent unused
    Verilated::timeunit(-12);
    Verilated::timeprecision(-12);
}

VvOhLegal::~VvOhLegal() {
    VL_DO_CLEAR(delete __VlSymsp, __VlSymsp = NULL);
}

void VvOhLegal::_eval_initial(VvOhLegal__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvOhLegal::_eval_initial\n"); );
    VvOhLegal* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
}

void VvOhLegal::final() {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvOhLegal::final\n"); );
    // Variables
    VvOhLegal__Syms* __restrict vlSymsp = this->__VlSymsp;
    VvOhLegal* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
}

void VvOhLegal::_eval_settle(VvOhLegal__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvOhLegal::_eval_settle\n"); );
    VvOhLegal* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    vlTOPp->_combo__TOP__1(vlSymsp);
}

void VvOhLegal::_ctor_var_reset() {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvOhLegal::_ctor_var_reset\n"); );
    // Body
    oh = VL_RAND_RESET_I(8);
    legal = VL_RAND_RESET_I(1);
}
