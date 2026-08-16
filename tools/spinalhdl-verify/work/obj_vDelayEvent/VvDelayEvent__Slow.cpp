// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See VvDelayEvent.h for the primary calling header

#include "VvDelayEvent.h"
#include "VvDelayEvent__Syms.h"

//==========
CData/*0:0*/ VvDelayEvent::__Vtable1_vDelayEvent__DOT__d_run[16];
CData/*1:0*/ VvDelayEvent::__Vtable1_vDelayEvent__DOT__d_cnt[16];

VL_CTOR_IMP(VvDelayEvent) {
    VvDelayEvent__Syms* __restrict vlSymsp = __VlSymsp = new VvDelayEvent__Syms(this, name());
    VvDelayEvent* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Reset internal values
    
    // Reset structure values
    _ctor_var_reset();
}

void VvDelayEvent::__Vconfigure(VvDelayEvent__Syms* vlSymsp, bool first) {
    if (false && first) {}  // Prevent unused
    this->__VlSymsp = vlSymsp;
    if (false && this->__VlSymsp) {}  // Prevent unused
    Verilated::timeunit(-12);
    Verilated::timeprecision(-12);
}

VvDelayEvent::~VvDelayEvent() {
    VL_DO_CLEAR(delete __VlSymsp, __VlSymsp = NULL);
}

void VvDelayEvent::_settle__TOP__2(VvDelayEvent__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvDelayEvent::_settle__TOP__2\n"); );
    VvDelayEvent* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    vlTOPp->de = ((IData)(vlTOPp->vDelayEvent__DOT__d_run) 
                  & (3U == (IData)(vlTOPp->vDelayEvent__DOT__d_cnt)));
}

void VvDelayEvent::_eval_initial(VvDelayEvent__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvDelayEvent::_eval_initial\n"); );
    VvDelayEvent* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    vlTOPp->__Vclklast__TOP__clk = vlTOPp->clk;
    vlTOPp->__Vclklast__TOP__reset = vlTOPp->reset;
}

void VvDelayEvent::final() {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvDelayEvent::final\n"); );
    // Variables
    VvDelayEvent__Syms* __restrict vlSymsp = this->__VlSymsp;
    VvDelayEvent* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
}

void VvDelayEvent::_eval_settle(VvDelayEvent__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvDelayEvent::_eval_settle\n"); );
    VvDelayEvent* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    vlTOPp->_settle__TOP__2(vlSymsp);
}

void VvDelayEvent::_ctor_var_reset() {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvDelayEvent::_ctor_var_reset\n"); );
    // Body
    ev = VL_RAND_RESET_I(1);
    de = VL_RAND_RESET_I(1);
    clk = VL_RAND_RESET_I(1);
    reset = VL_RAND_RESET_I(1);
    vDelayEvent__DOT__d_run = VL_RAND_RESET_I(1);
    vDelayEvent__DOT__d_cnt = VL_RAND_RESET_I(2);
    __Vtablechg1[0] = 2U;
    __Vtablechg1[1] = 3U;
    __Vtablechg1[2] = 2U;
    __Vtablechg1[3] = 3U;
    __Vtablechg1[4] = 2U;
    __Vtablechg1[5] = 3U;
    __Vtablechg1[6] = 3U;
    __Vtablechg1[7] = 3U;
    __Vtablechg1[8] = 3U;
    __Vtablechg1[9] = 3U;
    __Vtablechg1[10] = 3U;
    __Vtablechg1[11] = 3U;
    __Vtablechg1[12] = 3U;
    __Vtablechg1[13] = 3U;
    __Vtablechg1[14] = 3U;
    __Vtablechg1[15] = 3U;
    __Vtable1_vDelayEvent__DOT__d_run[0] = 0U;
    __Vtable1_vDelayEvent__DOT__d_run[1] = 0U;
    __Vtable1_vDelayEvent__DOT__d_run[2] = 0U;
    __Vtable1_vDelayEvent__DOT__d_run[3] = 0U;
    __Vtable1_vDelayEvent__DOT__d_run[4] = 0U;
    __Vtable1_vDelayEvent__DOT__d_run[5] = 0U;
    __Vtable1_vDelayEvent__DOT__d_run[6] = 0U;
    __Vtable1_vDelayEvent__DOT__d_run[7] = 0U;
    __Vtable1_vDelayEvent__DOT__d_run[8] = 1U;
    __Vtable1_vDelayEvent__DOT__d_run[9] = 0U;
    __Vtable1_vDelayEvent__DOT__d_run[10] = 1U;
    __Vtable1_vDelayEvent__DOT__d_run[11] = 0U;
    __Vtable1_vDelayEvent__DOT__d_run[12] = 1U;
    __Vtable1_vDelayEvent__DOT__d_run[13] = 0U;
    __Vtable1_vDelayEvent__DOT__d_run[14] = 1U;
    __Vtable1_vDelayEvent__DOT__d_run[15] = 0U;
    __Vtable1_vDelayEvent__DOT__d_cnt[0] = 1U;
    __Vtable1_vDelayEvent__DOT__d_cnt[1] = 0U;
    __Vtable1_vDelayEvent__DOT__d_cnt[2] = 2U;
    __Vtable1_vDelayEvent__DOT__d_cnt[3] = 0U;
    __Vtable1_vDelayEvent__DOT__d_cnt[4] = 3U;
    __Vtable1_vDelayEvent__DOT__d_cnt[5] = 0U;
    __Vtable1_vDelayEvent__DOT__d_cnt[6] = 0U;
    __Vtable1_vDelayEvent__DOT__d_cnt[7] = 0U;
    __Vtable1_vDelayEvent__DOT__d_cnt[8] = 0U;
    __Vtable1_vDelayEvent__DOT__d_cnt[9] = 0U;
    __Vtable1_vDelayEvent__DOT__d_cnt[10] = 0U;
    __Vtable1_vDelayEvent__DOT__d_cnt[11] = 0U;
    __Vtable1_vDelayEvent__DOT__d_cnt[12] = 0U;
    __Vtable1_vDelayEvent__DOT__d_cnt[13] = 0U;
    __Vtable1_vDelayEvent__DOT__d_cnt[14] = 0U;
    __Vtable1_vDelayEvent__DOT__d_cnt[15] = 0U;
}
