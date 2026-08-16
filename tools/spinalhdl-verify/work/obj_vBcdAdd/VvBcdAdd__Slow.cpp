// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See VvBcdAdd.h for the primary calling header

#include "VvBcdAdd.h"
#include "VvBcdAdd__Syms.h"

//==========

VL_CTOR_IMP(VvBcdAdd) {
    VvBcdAdd__Syms* __restrict vlSymsp = __VlSymsp = new VvBcdAdd__Syms(this, name());
    VvBcdAdd* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Reset internal values
    
    // Reset structure values
    _ctor_var_reset();
}

void VvBcdAdd::__Vconfigure(VvBcdAdd__Syms* vlSymsp, bool first) {
    if (false && first) {}  // Prevent unused
    this->__VlSymsp = vlSymsp;
    if (false && this->__VlSymsp) {}  // Prevent unused
    Verilated::timeunit(-12);
    Verilated::timeprecision(-12);
}

VvBcdAdd::~VvBcdAdd() {
    VL_DO_CLEAR(delete __VlSymsp, __VlSymsp = NULL);
}

void VvBcdAdd::_eval_initial(VvBcdAdd__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvBcdAdd::_eval_initial\n"); );
    VvBcdAdd* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
}

void VvBcdAdd::final() {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvBcdAdd::final\n"); );
    // Variables
    VvBcdAdd__Syms* __restrict vlSymsp = this->__VlSymsp;
    VvBcdAdd* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
}

void VvBcdAdd::_eval_settle(VvBcdAdd__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvBcdAdd::_eval_settle\n"); );
    VvBcdAdd* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    vlTOPp->_combo__TOP__1(vlSymsp);
}

void VvBcdAdd::_ctor_var_reset() {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvBcdAdd::_ctor_var_reset\n"); );
    // Body
    a = VL_RAND_RESET_I(4);
    b = VL_RAND_RESET_I(4);
    cin = VL_RAND_RESET_I(1);
    s = VL_RAND_RESET_I(4);
    co = VL_RAND_RESET_I(1);
}
