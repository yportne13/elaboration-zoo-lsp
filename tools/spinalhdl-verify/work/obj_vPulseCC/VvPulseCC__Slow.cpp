// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See VvPulseCC.h for the primary calling header

#include "VvPulseCC.h"
#include "VvPulseCC__Syms.h"

//==========

VL_CTOR_IMP(VvPulseCC) {
    VvPulseCC__Syms* __restrict vlSymsp = __VlSymsp = new VvPulseCC__Syms(this, name());
    VvPulseCC* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Reset internal values
    
    // Reset structure values
    _ctor_var_reset();
}

void VvPulseCC::__Vconfigure(VvPulseCC__Syms* vlSymsp, bool first) {
    if (false && first) {}  // Prevent unused
    this->__VlSymsp = vlSymsp;
    if (false && this->__VlSymsp) {}  // Prevent unused
    Verilated::timeunit(-12);
    Verilated::timeprecision(-12);
}

VvPulseCC::~VvPulseCC() {
    VL_DO_CLEAR(delete __VlSymsp, __VlSymsp = NULL);
}

void VvPulseCC::_settle__TOP__3(VvPulseCC__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvPulseCC::_settle__TOP__3\n"); );
    VvPulseCC* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    vlTOPp->pulseOut = ((IData)(vlTOPp->vPulseCC__DOT_____05Fsync1) 
                        ^ (IData)(vlTOPp->vPulseCC__DOT_____05Fsync2));
}

void VvPulseCC::_eval_initial(VvPulseCC__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvPulseCC::_eval_initial\n"); );
    VvPulseCC* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    vlTOPp->__Vclklast__TOP__clkA = vlTOPp->clkA;
    vlTOPp->__Vclklast__TOP__clkB = vlTOPp->clkB;
}

void VvPulseCC::final() {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvPulseCC::final\n"); );
    // Variables
    VvPulseCC__Syms* __restrict vlSymsp = this->__VlSymsp;
    VvPulseCC* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
}

void VvPulseCC::_eval_settle(VvPulseCC__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvPulseCC::_eval_settle\n"); );
    VvPulseCC* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    vlTOPp->_settle__TOP__3(vlSymsp);
}

void VvPulseCC::_ctor_var_reset() {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvPulseCC::_ctor_var_reset\n"); );
    // Body
    pulseIn = VL_RAND_RESET_I(1);
    pulseOut = VL_RAND_RESET_I(1);
    clkA = VL_RAND_RESET_I(1);
    clkB = VL_RAND_RESET_I(1);
    vPulseCC__DOT_____05Ftoggle = VL_RAND_RESET_I(1);
    vPulseCC__DOT_____05Fsync1 = VL_RAND_RESET_I(1);
    vPulseCC__DOT_____05Fsync2 = VL_RAND_RESET_I(1);
    __Vdly__vPulseCC__DOT_____05Ftoggle = VL_RAND_RESET_I(1);
}
