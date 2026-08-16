// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See VvMinMax.h for the primary calling header

#include "VvMinMax.h"
#include "VvMinMax__Syms.h"

//==========

VL_CTOR_IMP(VvMinMax) {
    VvMinMax__Syms* __restrict vlSymsp = __VlSymsp = new VvMinMax__Syms(this, name());
    VvMinMax* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Reset internal values
    
    // Reset structure values
    _ctor_var_reset();
}

void VvMinMax::__Vconfigure(VvMinMax__Syms* vlSymsp, bool first) {
    if (false && first) {}  // Prevent unused
    this->__VlSymsp = vlSymsp;
    if (false && this->__VlSymsp) {}  // Prevent unused
    Verilated::timeunit(-12);
    Verilated::timeprecision(-12);
}

VvMinMax::~VvMinMax() {
    VL_DO_CLEAR(delete __VlSymsp, __VlSymsp = NULL);
}

void VvMinMax::_eval_initial(VvMinMax__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvMinMax::_eval_initial\n"); );
    VvMinMax* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
}

void VvMinMax::final() {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvMinMax::final\n"); );
    // Variables
    VvMinMax__Syms* __restrict vlSymsp = this->__VlSymsp;
    VvMinMax* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
}

void VvMinMax::_eval_settle(VvMinMax__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvMinMax::_eval_settle\n"); );
    VvMinMax* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    vlTOPp->_combo__TOP__1(vlSymsp);
}

void VvMinMax::_ctor_var_reset() {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvMinMax::_ctor_var_reset\n"); );
    // Body
    a = VL_RAND_RESET_I(8);
    b = VL_RAND_RESET_I(8);
    mn = VL_RAND_RESET_I(8);
    mx = VL_RAND_RESET_I(8);
}
