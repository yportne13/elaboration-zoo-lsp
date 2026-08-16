// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See VvWatchdog.h for the primary calling header

#include "VvWatchdog.h"
#include "VvWatchdog__Syms.h"

//==========

void VvWatchdog::eval_step() {
    VL_DEBUG_IF(VL_DBG_MSGF("+++++TOP Evaluate VvWatchdog::eval\n"); );
    VvWatchdog__Syms* __restrict vlSymsp = this->__VlSymsp;  // Setup global symbol table
    VvWatchdog* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
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
            VL_FATAL_MT("/mnt/f/projects/hermes/elaboration-zoo-lsp/tools/spinalhdl-verify/work/vWatchdog.v", 1, "",
                "Verilated model didn't converge\n"
                "- See DIDNOTCONVERGE in the Verilator manual");
        } else {
            __Vchange = _change_request(vlSymsp);
        }
    } while (VL_UNLIKELY(__Vchange));
}

void VvWatchdog::_eval_initial_loop(VvWatchdog__Syms* __restrict vlSymsp) {
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
            VL_FATAL_MT("/mnt/f/projects/hermes/elaboration-zoo-lsp/tools/spinalhdl-verify/work/vWatchdog.v", 1, "",
                "Verilated model didn't DC converge\n"
                "- See DIDNOTCONVERGE in the Verilator manual");
        } else {
            __Vchange = _change_request(vlSymsp);
        }
    } while (VL_UNLIKELY(__Vchange));
}

VL_INLINE_OPT void VvWatchdog::_sequent__TOP__1(VvWatchdog__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvWatchdog::_sequent__TOP__1\n"); );
    VvWatchdog* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Variables
    CData/*7:0*/ __Vdly__vWatchdog__DOT_____05Fcnt;
    // Body
    __Vdly__vWatchdog__DOT_____05Fcnt = vlTOPp->vWatchdog__DOT_____05Fcnt;
    if (vlTOPp->reset) {
        __Vdly__vWatchdog__DOT_____05Fcnt = 0U;
        vlTOPp->vWatchdog__DOT_____05Ftimeout = 0U;
    } else {
        if (((IData)(vlTOPp->vWatchdog__DOT_____05Fcnt) 
             == (IData)(vlTOPp->lim))) {
            vlTOPp->vWatchdog__DOT_____05Ftimeout = 1U;
        }
        if (((IData)(vlTOPp->vWatchdog__DOT_____05Fcnt) 
             == (IData)(vlTOPp->lim))) {
            __Vdly__vWatchdog__DOT_____05Fcnt = 0U;
        }
        if (vlTOPp->feed) {
            vlTOPp->vWatchdog__DOT_____05Ftimeout = 0U;
        }
        if (vlTOPp->feed) {
            __Vdly__vWatchdog__DOT_____05Fcnt = 0U;
        }
        if (((~ (IData)(vlTOPp->feed)) & ((IData)(vlTOPp->vWatchdog__DOT_____05Fcnt) 
                                          != (IData)(vlTOPp->lim)))) {
            __Vdly__vWatchdog__DOT_____05Fcnt = (0xffU 
                                                 & ((IData)(1U) 
                                                    + (IData)(vlTOPp->vWatchdog__DOT_____05Fcnt)));
        }
    }
    vlTOPp->vWatchdog__DOT_____05Fcnt = __Vdly__vWatchdog__DOT_____05Fcnt;
    vlTOPp->timeout = vlTOPp->vWatchdog__DOT_____05Ftimeout;
}

void VvWatchdog::_eval(VvWatchdog__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvWatchdog::_eval\n"); );
    VvWatchdog* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    if ((((IData)(vlTOPp->clk) & (~ (IData)(vlTOPp->__Vclklast__TOP__clk))) 
         | ((IData)(vlTOPp->reset) & (~ (IData)(vlTOPp->__Vclklast__TOP__reset))))) {
        vlTOPp->_sequent__TOP__1(vlSymsp);
    }
    // Final
    vlTOPp->__Vclklast__TOP__clk = vlTOPp->clk;
    vlTOPp->__Vclklast__TOP__reset = vlTOPp->reset;
}

VL_INLINE_OPT QData VvWatchdog::_change_request(VvWatchdog__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvWatchdog::_change_request\n"); );
    VvWatchdog* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    return (vlTOPp->_change_request_1(vlSymsp));
}

VL_INLINE_OPT QData VvWatchdog::_change_request_1(VvWatchdog__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvWatchdog::_change_request_1\n"); );
    VvWatchdog* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    // Change detection
    QData __req = false;  // Logically a bool
    return __req;
}

#ifdef VL_DEBUG
void VvWatchdog::_eval_debug_assertions() {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvWatchdog::_eval_debug_assertions\n"); );
    // Body
    if (VL_UNLIKELY((feed & 0xfeU))) {
        Verilated::overWidthError("feed");}
    if (VL_UNLIKELY((clk & 0xfeU))) {
        Verilated::overWidthError("clk");}
    if (VL_UNLIKELY((reset & 0xfeU))) {
        Verilated::overWidthError("reset");}
}
#endif  // VL_DEBUG
