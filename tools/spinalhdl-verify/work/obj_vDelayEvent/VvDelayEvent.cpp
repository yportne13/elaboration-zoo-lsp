// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See VvDelayEvent.h for the primary calling header

#include "VvDelayEvent.h"
#include "VvDelayEvent__Syms.h"

//==========

void VvDelayEvent::eval_step() {
    VL_DEBUG_IF(VL_DBG_MSGF("+++++TOP Evaluate VvDelayEvent::eval\n"); );
    VvDelayEvent__Syms* __restrict vlSymsp = this->__VlSymsp;  // Setup global symbol table
    VvDelayEvent* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
#ifdef VL_DEBUG
    // Debug assertions
    _eval_debug_assertions();
#endif  // VL_DEBUG
    // Initialize
    if (VL_UNLIKELY(!vlSymsp->__Vm_didInit)) _eval_initial_loop(vlSymsp);
    // Evaluate till stable
    int __VclockLoop = 0;
    QData __Vchange = 1;
    do {
        VL_DEBUG_IF(VL_DBG_MSGF("+ Clock loop\n"););
        _eval(vlSymsp);
        if (VL_UNLIKELY(++__VclockLoop > 100)) {
            // About to fail, so enable debug to see what's not settling.
            // Note you must run make with OPT=-DVL_DEBUG for debug prints.
            int __Vsaved_debug = Verilated::debug();
            Verilated::debug(1);
            __Vchange = _change_request(vlSymsp);
            Verilated::debug(__Vsaved_debug);
            VL_FATAL_MT("/mnt/f/projects/hermes/elaboration-zoo-lsp/tools/spinalhdl-verify/work/vDelayEvent.v", 1, "",
                "Verilated model didn't converge\n"
                "- See DIDNOTCONVERGE in the Verilator manual");
        } else {
            __Vchange = _change_request(vlSymsp);
        }
    } while (VL_UNLIKELY(__Vchange));
}

void VvDelayEvent::_eval_initial_loop(VvDelayEvent__Syms* __restrict vlSymsp) {
    vlSymsp->__Vm_didInit = true;
    _eval_initial(vlSymsp);
    // Evaluate till stable
    int __VclockLoop = 0;
    QData __Vchange = 1;
    do {
        _eval_settle(vlSymsp);
        _eval(vlSymsp);
        if (VL_UNLIKELY(++__VclockLoop > 100)) {
            // About to fail, so enable debug to see what's not settling.
            // Note you must run make with OPT=-DVL_DEBUG for debug prints.
            int __Vsaved_debug = Verilated::debug();
            Verilated::debug(1);
            __Vchange = _change_request(vlSymsp);
            Verilated::debug(__Vsaved_debug);
            VL_FATAL_MT("/mnt/f/projects/hermes/elaboration-zoo-lsp/tools/spinalhdl-verify/work/vDelayEvent.v", 1, "",
                "Verilated model didn't DC converge\n"
                "- See DIDNOTCONVERGE in the Verilator manual");
        } else {
            __Vchange = _change_request(vlSymsp);
        }
    } while (VL_UNLIKELY(__Vchange));
}

VL_INLINE_OPT void VvDelayEvent::_sequent__TOP__1(VvDelayEvent__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvDelayEvent::_sequent__TOP__1\n"); );
    VvDelayEvent* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Variables
    CData/*3:0*/ __Vtableidx1;
    // Body
    __Vtableidx1 = (((IData)(vlTOPp->ev) << 3U) | (
                                                   ((IData)(vlTOPp->vDelayEvent__DOT__d_cnt) 
                                                    << 1U) 
                                                   | (IData)(vlTOPp->reset)));
    if ((1U & vlTOPp->__Vtablechg1[__Vtableidx1])) {
        vlTOPp->vDelayEvent__DOT__d_run = vlTOPp->__Vtable1_vDelayEvent__DOT__d_run
            [__Vtableidx1];
    }
    vlTOPp->vDelayEvent__DOT__d_cnt = vlTOPp->__Vtable1_vDelayEvent__DOT__d_cnt
        [__Vtableidx1];
    vlTOPp->de = ((IData)(vlTOPp->vDelayEvent__DOT__d_run) 
                  & (3U == (IData)(vlTOPp->vDelayEvent__DOT__d_cnt)));
}

void VvDelayEvent::_eval(VvDelayEvent__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvDelayEvent::_eval\n"); );
    VvDelayEvent* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    if ((((IData)(vlTOPp->clk) & (~ (IData)(vlTOPp->__Vclklast__TOP__clk))) 
         | ((IData)(vlTOPp->reset) & (~ (IData)(vlTOPp->__Vclklast__TOP__reset))))) {
        vlTOPp->_sequent__TOP__1(vlSymsp);
    }
    // Final
    vlTOPp->__Vclklast__TOP__clk = vlTOPp->clk;
    vlTOPp->__Vclklast__TOP__reset = vlTOPp->reset;
}

VL_INLINE_OPT QData VvDelayEvent::_change_request(VvDelayEvent__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvDelayEvent::_change_request\n"); );
    VvDelayEvent* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    return (vlTOPp->_change_request_1(vlSymsp));
}

VL_INLINE_OPT QData VvDelayEvent::_change_request_1(VvDelayEvent__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvDelayEvent::_change_request_1\n"); );
    VvDelayEvent* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    // Change detection
    QData __req = false;  // Logically a bool
    return __req;
}

#ifdef VL_DEBUG
void VvDelayEvent::_eval_debug_assertions() {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvDelayEvent::_eval_debug_assertions\n"); );
    // Body
    if (VL_UNLIKELY((ev & 0xfeU))) {
        Verilated::overWidthError("ev");}
    if (VL_UNLIKELY((clk & 0xfeU))) {
        Verilated::overWidthError("clk");}
    if (VL_UNLIKELY((reset & 0xfeU))) {
        Verilated::overWidthError("reset");}
}
#endif  // VL_DEBUG
