// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See VvDecoder.h for the primary calling header

#include "VvDecoder.h"
#include "VvDecoder__Syms.h"

//==========

VL_CTOR_IMP(VvDecoder) {
    VvDecoder__Syms* __restrict vlSymsp = __VlSymsp = new VvDecoder__Syms(this, name());
    VvDecoder* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Reset internal values
    
    // Reset structure values
    _ctor_var_reset();
}

void VvDecoder::__Vconfigure(VvDecoder__Syms* vlSymsp, bool first) {
    if (false && first) {}  // Prevent unused
    this->__VlSymsp = vlSymsp;
    if (false && this->__VlSymsp) {}  // Prevent unused
    Verilated::timeunit(-12);
    Verilated::timeprecision(-12);
}

VvDecoder::~VvDecoder() {
    VL_DO_CLEAR(delete __VlSymsp, __VlSymsp = NULL);
}

void VvDecoder::_eval_initial(VvDecoder__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvDecoder::_eval_initial\n"); );
    VvDecoder* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
}

void VvDecoder::final() {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvDecoder::final\n"); );
    // Variables
    VvDecoder__Syms* __restrict vlSymsp = this->__VlSymsp;
    VvDecoder* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
}

void VvDecoder::_eval_settle(VvDecoder__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvDecoder::_eval_settle\n"); );
    VvDecoder* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    vlTOPp->_combo__TOP__1(vlSymsp);
}

void VvDecoder::_ctor_var_reset() {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvDecoder::_ctor_var_reset\n"); );
    // Body
    oh = VL_RAND_RESET_I(4);
    idx = VL_RAND_RESET_I(2);
}
