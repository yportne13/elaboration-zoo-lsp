// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See VvOhFirst.h for the primary calling header

#include "VvOhFirst.h"
#include "VvOhFirst__Syms.h"

//==========

VL_CTOR_IMP(VvOhFirst) {
    VvOhFirst__Syms* __restrict vlSymsp = __VlSymsp = new VvOhFirst__Syms(this, name());
    VvOhFirst* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Reset internal values
    
    // Reset structure values
    _ctor_var_reset();
}

void VvOhFirst::__Vconfigure(VvOhFirst__Syms* vlSymsp, bool first) {
    if (false && first) {}  // Prevent unused
    this->__VlSymsp = vlSymsp;
    if (false && this->__VlSymsp) {}  // Prevent unused
    Verilated::timeunit(-12);
    Verilated::timeprecision(-12);
}

VvOhFirst::~VvOhFirst() {
    VL_DO_CLEAR(delete __VlSymsp, __VlSymsp = NULL);
}

void VvOhFirst::_eval_initial(VvOhFirst__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvOhFirst::_eval_initial\n"); );
    VvOhFirst* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
}

void VvOhFirst::final() {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvOhFirst::final\n"); );
    // Variables
    VvOhFirst__Syms* __restrict vlSymsp = this->__VlSymsp;
    VvOhFirst* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
}

void VvOhFirst::_eval_settle(VvOhFirst__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvOhFirst::_eval_settle\n"); );
    VvOhFirst* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    vlTOPp->_combo__TOP__1(vlSymsp);
}

void VvOhFirst::_ctor_var_reset() {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvOhFirst::_ctor_var_reset\n"); );
    // Body
    oh = VL_RAND_RESET_I(8);
    f = VL_RAND_RESET_I(8);
}
