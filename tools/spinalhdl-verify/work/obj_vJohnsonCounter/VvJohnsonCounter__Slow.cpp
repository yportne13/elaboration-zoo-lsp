// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See VvJohnsonCounter.h for the primary calling header

#include "VvJohnsonCounter.h"
#include "VvJohnsonCounter__Syms.h"

//==========
CData/*3:0*/ VvJohnsonCounter::__Vtable1_vJohnsonCounter__DOT__jc[32];

VL_CTOR_IMP(VvJohnsonCounter) {
    VvJohnsonCounter__Syms* __restrict vlSymsp = __VlSymsp = new VvJohnsonCounter__Syms(this, name());
    VvJohnsonCounter* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Reset internal values
    
    // Reset structure values
    _ctor_var_reset();
}

void VvJohnsonCounter::__Vconfigure(VvJohnsonCounter__Syms* vlSymsp, bool first) {
    if (false && first) {}  // Prevent unused
    this->__VlSymsp = vlSymsp;
    if (false && this->__VlSymsp) {}  // Prevent unused
    Verilated::timeunit(-12);
    Verilated::timeprecision(-12);
}

VvJohnsonCounter::~VvJohnsonCounter() {
    VL_DO_CLEAR(delete __VlSymsp, __VlSymsp = NULL);
}

void VvJohnsonCounter::_settle__TOP__2(VvJohnsonCounter__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvJohnsonCounter::_settle__TOP__2\n"); );
    VvJohnsonCounter* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    vlTOPp->value = vlTOPp->vJohnsonCounter__DOT__jc;
    vlTOPp->willOverflow = (1U & (((IData)(vlTOPp->vJohnsonCounter__DOT__jc) 
                                   >> 3U) & (~ ((IData)(vlTOPp->vJohnsonCounter__DOT__jc) 
                                                >> 2U))));
}

void VvJohnsonCounter::_eval_initial(VvJohnsonCounter__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvJohnsonCounter::_eval_initial\n"); );
    VvJohnsonCounter* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    vlTOPp->__Vclklast__TOP__clk = vlTOPp->clk;
    vlTOPp->__Vclklast__TOP__reset = vlTOPp->reset;
}

void VvJohnsonCounter::final() {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvJohnsonCounter::final\n"); );
    // Variables
    VvJohnsonCounter__Syms* __restrict vlSymsp = this->__VlSymsp;
    VvJohnsonCounter* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
}

void VvJohnsonCounter::_eval_settle(VvJohnsonCounter__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvJohnsonCounter::_eval_settle\n"); );
    VvJohnsonCounter* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    vlTOPp->_settle__TOP__2(vlSymsp);
}

void VvJohnsonCounter::_ctor_var_reset() {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvJohnsonCounter::_ctor_var_reset\n"); );
    // Body
    en = VL_RAND_RESET_I(1);
    value = VL_RAND_RESET_I(4);
    willOverflow = VL_RAND_RESET_I(1);
    clk = VL_RAND_RESET_I(1);
    reset = VL_RAND_RESET_I(1);
    vJohnsonCounter__DOT__jc = VL_RAND_RESET_I(4);
    __Vtable1_vJohnsonCounter__DOT__jc[0] = 1U;
    __Vtable1_vJohnsonCounter__DOT__jc[1] = 0U;
    __Vtable1_vJohnsonCounter__DOT__jc[2] = 3U;
    __Vtable1_vJohnsonCounter__DOT__jc[3] = 0U;
    __Vtable1_vJohnsonCounter__DOT__jc[4] = 5U;
    __Vtable1_vJohnsonCounter__DOT__jc[5] = 0U;
    __Vtable1_vJohnsonCounter__DOT__jc[6] = 7U;
    __Vtable1_vJohnsonCounter__DOT__jc[7] = 0U;
    __Vtable1_vJohnsonCounter__DOT__jc[8] = 9U;
    __Vtable1_vJohnsonCounter__DOT__jc[9] = 0U;
    __Vtable1_vJohnsonCounter__DOT__jc[10] = 0xbU;
    __Vtable1_vJohnsonCounter__DOT__jc[11] = 0U;
    __Vtable1_vJohnsonCounter__DOT__jc[12] = 0xdU;
    __Vtable1_vJohnsonCounter__DOT__jc[13] = 0U;
    __Vtable1_vJohnsonCounter__DOT__jc[14] = 0xfU;
    __Vtable1_vJohnsonCounter__DOT__jc[15] = 0U;
    __Vtable1_vJohnsonCounter__DOT__jc[16] = 0U;
    __Vtable1_vJohnsonCounter__DOT__jc[17] = 0U;
    __Vtable1_vJohnsonCounter__DOT__jc[18] = 0U;
    __Vtable1_vJohnsonCounter__DOT__jc[19] = 0U;
    __Vtable1_vJohnsonCounter__DOT__jc[20] = 0U;
    __Vtable1_vJohnsonCounter__DOT__jc[21] = 0U;
    __Vtable1_vJohnsonCounter__DOT__jc[22] = 0U;
    __Vtable1_vJohnsonCounter__DOT__jc[23] = 0U;
    __Vtable1_vJohnsonCounter__DOT__jc[24] = 8U;
    __Vtable1_vJohnsonCounter__DOT__jc[25] = 0U;
    __Vtable1_vJohnsonCounter__DOT__jc[26] = 0xaU;
    __Vtable1_vJohnsonCounter__DOT__jc[27] = 0U;
    __Vtable1_vJohnsonCounter__DOT__jc[28] = 0xcU;
    __Vtable1_vJohnsonCounter__DOT__jc[29] = 0U;
    __Vtable1_vJohnsonCounter__DOT__jc[30] = 0xeU;
    __Vtable1_vJohnsonCounter__DOT__jc[31] = 0U;
}
