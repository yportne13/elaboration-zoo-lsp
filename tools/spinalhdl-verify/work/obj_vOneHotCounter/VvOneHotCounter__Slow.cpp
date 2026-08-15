// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See VvOneHotCounter.h for the primary calling header

#include "VvOneHotCounter.h"
#include "VvOneHotCounter__Syms.h"

//==========

VL_CTOR_IMP(VvOneHotCounter) {
    VvOneHotCounter__Syms* __restrict vlSymsp = __VlSymsp = new VvOneHotCounter__Syms(this, name());
    VvOneHotCounter* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Reset internal values
    
    // Reset structure values
    _ctor_var_reset();
}

void VvOneHotCounter::__Vconfigure(VvOneHotCounter__Syms* vlSymsp, bool first) {
    if (false && first) {}  // Prevent unused
    this->__VlSymsp = vlSymsp;
    if (false && this->__VlSymsp) {}  // Prevent unused
    Verilated::timeunit(-12);
    Verilated::timeprecision(-12);
}

VvOneHotCounter::~VvOneHotCounter() {
    VL_DO_CLEAR(delete __VlSymsp, __VlSymsp = NULL);
}

void VvOneHotCounter::_settle__TOP__2(VvOneHotCounter__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvOneHotCounter::_settle__TOP__2\n"); );
    VvOneHotCounter* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    vlTOPp->value = vlTOPp->vOneHotCounter__DOT__ohc;
    vlTOPp->willOverflow = (1U & ((IData)(vlTOPp->vOneHotCounter__DOT__ohc) 
                                  >> 3U));
}

void VvOneHotCounter::_eval_initial(VvOneHotCounter__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvOneHotCounter::_eval_initial\n"); );
    VvOneHotCounter* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    vlTOPp->__Vclklast__TOP__clk = vlTOPp->clk;
    vlTOPp->__Vclklast__TOP__reset = vlTOPp->reset;
}

void VvOneHotCounter::final() {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvOneHotCounter::final\n"); );
    // Variables
    VvOneHotCounter__Syms* __restrict vlSymsp = this->__VlSymsp;
    VvOneHotCounter* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
}

void VvOneHotCounter::_eval_settle(VvOneHotCounter__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvOneHotCounter::_eval_settle\n"); );
    VvOneHotCounter* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    vlTOPp->_settle__TOP__2(vlSymsp);
}

void VvOneHotCounter::_ctor_var_reset() {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvOneHotCounter::_ctor_var_reset\n"); );
    // Body
    en = VL_RAND_RESET_I(1);
    value = VL_RAND_RESET_I(4);
    willOverflow = VL_RAND_RESET_I(1);
    clk = VL_RAND_RESET_I(1);
    reset = VL_RAND_RESET_I(1);
    vOneHotCounter__DOT__ohc = VL_RAND_RESET_I(4);
}
