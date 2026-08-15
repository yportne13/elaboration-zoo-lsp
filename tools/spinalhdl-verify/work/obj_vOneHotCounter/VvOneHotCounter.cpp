// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See VvOneHotCounter.h for the primary calling header

#include "VvOneHotCounter.h"
#include "VvOneHotCounter__Syms.h"

//==========

void VvOneHotCounter::eval_step() {
    VL_DEBUG_IF(VL_DBG_MSGF("+++++TOP Evaluate VvOneHotCounter::eval\n"); );
    VvOneHotCounter__Syms* __restrict vlSymsp = this->__VlSymsp;  // Setup global symbol table
    VvOneHotCounter* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
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
            VL_FATAL_MT("/mnt/f/projects/hermes/elaboration-zoo-lsp/tools/spinalhdl-verify/work/vOneHotCounter.v", 1, "",
                "Verilated model didn't converge\n"
                "- See DIDNOTCONVERGE in the Verilator manual");
        } else {
            __Vchange = _change_request(vlSymsp);
        }
    } while (VL_UNLIKELY(__Vchange));
}

void VvOneHotCounter::_eval_initial_loop(VvOneHotCounter__Syms* __restrict vlSymsp) {
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
            VL_FATAL_MT("/mnt/f/projects/hermes/elaboration-zoo-lsp/tools/spinalhdl-verify/work/vOneHotCounter.v", 1, "",
                "Verilated model didn't DC converge\n"
                "- See DIDNOTCONVERGE in the Verilator manual");
        } else {
            __Vchange = _change_request(vlSymsp);
        }
    } while (VL_UNLIKELY(__Vchange));
}

VL_INLINE_OPT void VvOneHotCounter::_sequent__TOP__1(VvOneHotCounter__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvOneHotCounter::_sequent__TOP__1\n"); );
    VvOneHotCounter* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Variables
    CData/*3:0*/ __Vdly__vOneHotCounter__DOT__ohc;
    // Body
    __Vdly__vOneHotCounter__DOT__ohc = vlTOPp->vOneHotCounter__DOT__ohc;
    if (vlTOPp->reset) {
        __Vdly__vOneHotCounter__DOT__ohc = 1U;
    } else {
        if ((8U & (IData)(vlTOPp->vOneHotCounter__DOT__ohc))) {
            __Vdly__vOneHotCounter__DOT__ohc = 1U;
        }
        if ((1U & (~ ((IData)(vlTOPp->vOneHotCounter__DOT__ohc) 
                      >> 3U)))) {
            __Vdly__vOneHotCounter__DOT__ohc = (0xfU 
                                                & ((IData)(vlTOPp->vOneHotCounter__DOT__ohc) 
                                                   << 1U));
        }
    }
    vlTOPp->vOneHotCounter__DOT__ohc = __Vdly__vOneHotCounter__DOT__ohc;
    vlTOPp->value = vlTOPp->vOneHotCounter__DOT__ohc;
    vlTOPp->willOverflow = (1U & ((IData)(vlTOPp->vOneHotCounter__DOT__ohc) 
                                  >> 3U));
}

void VvOneHotCounter::_eval(VvOneHotCounter__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvOneHotCounter::_eval\n"); );
    VvOneHotCounter* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    if ((((IData)(vlTOPp->clk) & (~ (IData)(vlTOPp->__Vclklast__TOP__clk))) 
         | ((IData)(vlTOPp->reset) & (~ (IData)(vlTOPp->__Vclklast__TOP__reset))))) {
        vlTOPp->_sequent__TOP__1(vlSymsp);
    }
    // Final
    vlTOPp->__Vclklast__TOP__clk = vlTOPp->clk;
    vlTOPp->__Vclklast__TOP__reset = vlTOPp->reset;
}

VL_INLINE_OPT QData VvOneHotCounter::_change_request(VvOneHotCounter__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvOneHotCounter::_change_request\n"); );
    VvOneHotCounter* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    return (vlTOPp->_change_request_1(vlSymsp));
}

VL_INLINE_OPT QData VvOneHotCounter::_change_request_1(VvOneHotCounter__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvOneHotCounter::_change_request_1\n"); );
    VvOneHotCounter* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    // Change detection
    QData __req = false;  // Logically a bool
    return __req;
}

#ifdef VL_DEBUG
void VvOneHotCounter::_eval_debug_assertions() {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvOneHotCounter::_eval_debug_assertions\n"); );
    // Body
    if (VL_UNLIKELY((en & 0xfeU))) {
        Verilated::overWidthError("en");}
    if (VL_UNLIKELY((clk & 0xfeU))) {
        Verilated::overWidthError("clk");}
    if (VL_UNLIKELY((reset & 0xfeU))) {
        Verilated::overWidthError("reset");}
}
#endif  // VL_DEBUG
