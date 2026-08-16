// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See VvMuxOH.h for the primary calling header

#include "VvMuxOH.h"
#include "VvMuxOH__Syms.h"

//==========

VL_CTOR_IMP(VvMuxOH) {
    VvMuxOH__Syms* __restrict vlSymsp = __VlSymsp = new VvMuxOH__Syms(this, name());
    VvMuxOH* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Reset internal values
    
    // Reset structure values
    _ctor_var_reset();
}

void VvMuxOH::__Vconfigure(VvMuxOH__Syms* vlSymsp, bool first) {
    if (false && first) {}  // Prevent unused
    this->__VlSymsp = vlSymsp;
    if (false && this->__VlSymsp) {}  // Prevent unused
    Verilated::timeunit(-12);
    Verilated::timeprecision(-12);
}

VvMuxOH::~VvMuxOH() {
    VL_DO_CLEAR(delete __VlSymsp, __VlSymsp = NULL);
}

void VvMuxOH::_eval_initial(VvMuxOH__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvMuxOH::_eval_initial\n"); );
    VvMuxOH* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
}

void VvMuxOH::final() {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvMuxOH::final\n"); );
    // Variables
    VvMuxOH__Syms* __restrict vlSymsp = this->__VlSymsp;
    VvMuxOH* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
}

void VvMuxOH::_eval_settle(VvMuxOH__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvMuxOH::_eval_settle\n"); );
    VvMuxOH* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    vlTOPp->_combo__TOP__1(vlSymsp);
}

void VvMuxOH::_ctor_var_reset() {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvMuxOH::_ctor_var_reset\n"); );
    // Body
    sel = VL_RAND_RESET_I(4);
    a = VL_RAND_RESET_I(8);
    b = VL_RAND_RESET_I(8);
    c = VL_RAND_RESET_I(8);
    d = VL_RAND_RESET_I(8);
    o = VL_RAND_RESET_I(8);
}
