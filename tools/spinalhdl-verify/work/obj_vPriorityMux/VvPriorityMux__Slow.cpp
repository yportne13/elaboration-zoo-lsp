// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See VvPriorityMux.h for the primary calling header

#include "VvPriorityMux.h"
#include "VvPriorityMux__Syms.h"

//==========

VL_CTOR_IMP(VvPriorityMux) {
    VvPriorityMux__Syms* __restrict vlSymsp = __VlSymsp = new VvPriorityMux__Syms(this, name());
    VvPriorityMux* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Reset internal values
    
    // Reset structure values
    _ctor_var_reset();
}

void VvPriorityMux::__Vconfigure(VvPriorityMux__Syms* vlSymsp, bool first) {
    if (false && first) {}  // Prevent unused
    this->__VlSymsp = vlSymsp;
    if (false && this->__VlSymsp) {}  // Prevent unused
    Verilated::timeunit(-12);
    Verilated::timeprecision(-12);
}

VvPriorityMux::~VvPriorityMux() {
    VL_DO_CLEAR(delete __VlSymsp, __VlSymsp = NULL);
}

void VvPriorityMux::_eval_initial(VvPriorityMux__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvPriorityMux::_eval_initial\n"); );
    VvPriorityMux* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
}

void VvPriorityMux::final() {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvPriorityMux::final\n"); );
    // Variables
    VvPriorityMux__Syms* __restrict vlSymsp = this->__VlSymsp;
    VvPriorityMux* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
}

void VvPriorityMux::_eval_settle(VvPriorityMux__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvPriorityMux::_eval_settle\n"); );
    VvPriorityMux* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    vlTOPp->_combo__TOP__1(vlSymsp);
}

void VvPriorityMux::_ctor_var_reset() {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvPriorityMux::_ctor_var_reset\n"); );
    // Body
    sel = VL_RAND_RESET_I(4);
    a = VL_RAND_RESET_I(8);
    b = VL_RAND_RESET_I(8);
    c = VL_RAND_RESET_I(8);
    d = VL_RAND_RESET_I(8);
    dflt = VL_RAND_RESET_I(8);
    o = VL_RAND_RESET_I(8);
}
