// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See VvOhToUInt.h for the primary calling header

#include "VvOhToUInt.h"
#include "VvOhToUInt__Syms.h"

//==========

VL_CTOR_IMP(VvOhToUInt) {
    VvOhToUInt__Syms* __restrict vlSymsp = __VlSymsp = new VvOhToUInt__Syms(this, name());
    VvOhToUInt* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Reset internal values
    
    // Reset structure values
    _ctor_var_reset();
}

void VvOhToUInt::__Vconfigure(VvOhToUInt__Syms* vlSymsp, bool first) {
    if (false && first) {}  // Prevent unused
    this->__VlSymsp = vlSymsp;
    if (false && this->__VlSymsp) {}  // Prevent unused
    Verilated::timeunit(-12);
    Verilated::timeprecision(-12);
}

VvOhToUInt::~VvOhToUInt() {
    VL_DO_CLEAR(delete __VlSymsp, __VlSymsp = NULL);
}

void VvOhToUInt::_eval_initial(VvOhToUInt__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvOhToUInt::_eval_initial\n"); );
    VvOhToUInt* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
}

void VvOhToUInt::final() {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvOhToUInt::final\n"); );
    // Variables
    VvOhToUInt__Syms* __restrict vlSymsp = this->__VlSymsp;
    VvOhToUInt* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
}

void VvOhToUInt::_eval_settle(VvOhToUInt__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvOhToUInt::_eval_settle\n"); );
    VvOhToUInt* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    vlTOPp->_combo__TOP__1(vlSymsp);
}

void VvOhToUInt::_ctor_var_reset() {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvOhToUInt::_ctor_var_reset\n"); );
    // Body
    oh = VL_RAND_RESET_I(8);
    idx = VL_RAND_RESET_I(3);
}
