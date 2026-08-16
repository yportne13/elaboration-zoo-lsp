// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See VvPropLsb.h for the primary calling header

#include "VvPropLsb.h"
#include "VvPropLsb__Syms.h"

//==========

VL_CTOR_IMP(VvPropLsb) {
    VvPropLsb__Syms* __restrict vlSymsp = __VlSymsp = new VvPropLsb__Syms(this, name());
    VvPropLsb* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Reset internal values
    
    // Reset structure values
    _ctor_var_reset();
}

void VvPropLsb::__Vconfigure(VvPropLsb__Syms* vlSymsp, bool first) {
    if (false && first) {}  // Prevent unused
    this->__VlSymsp = vlSymsp;
    if (false && this->__VlSymsp) {}  // Prevent unused
    Verilated::timeunit(-12);
    Verilated::timeprecision(-12);
}

VvPropLsb::~VvPropLsb() {
    VL_DO_CLEAR(delete __VlSymsp, __VlSymsp = NULL);
}

void VvPropLsb::_eval_initial(VvPropLsb__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvPropLsb::_eval_initial\n"); );
    VvPropLsb* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
}

void VvPropLsb::final() {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvPropLsb::final\n"); );
    // Variables
    VvPropLsb__Syms* __restrict vlSymsp = this->__VlSymsp;
    VvPropLsb* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
}

void VvPropLsb::_eval_settle(VvPropLsb__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvPropLsb::_eval_settle\n"); );
    VvPropLsb* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    vlTOPp->_combo__TOP__1(vlSymsp);
}

void VvPropLsb::_ctor_var_reset() {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvPropLsb::_ctor_var_reset\n"); );
    // Body
    a = VL_RAND_RESET_I(8);
    r = VL_RAND_RESET_I(8);
}
