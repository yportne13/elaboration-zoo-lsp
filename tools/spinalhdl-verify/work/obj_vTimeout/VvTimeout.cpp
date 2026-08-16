// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See VvTimeout.h for the primary calling header

#include "VvTimeout.h"
#include "VvTimeout__Syms.h"

//==========

void VvTimeout::eval_step() {
    VL_DEBUG_IF(VL_DBG_MSGF("+++++TOP Evaluate VvTimeout::eval\n"); );
    VvTimeout__Syms* __restrict vlSymsp = this->__VlSymsp;  // Setup global symbol table
    VvTimeout* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
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
            VL_FATAL_MT("/mnt/f/projects/hermes/elaboration-zoo-lsp/tools/spinalhdl-verify/work/vTimeout.v", 1, "",
                "Verilated model didn't converge\n"
                "- See DIDNOTCONVERGE in the Verilator manual");
        } else {
            __Vchange = _change_request(vlSymsp);
        }
    } while (VL_UNLIKELY(__Vchange));
}

void VvTimeout::_eval_initial_loop(VvTimeout__Syms* __restrict vlSymsp) {
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
            VL_FATAL_MT("/mnt/f/projects/hermes/elaboration-zoo-lsp/tools/spinalhdl-verify/work/vTimeout.v", 1, "",
                "Verilated model didn't DC converge\n"
                "- See DIDNOTCONVERGE in the Verilator manual");
        } else {
            __Vchange = _change_request(vlSymsp);
        }
    } while (VL_UNLIKELY(__Vchange));
}

VL_INLINE_OPT void VvTimeout::_sequent__TOP__1(VvTimeout__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvTimeout::_sequent__TOP__1\n"); );
    VvTimeout* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Variables
    CData/*2:0*/ __Vdly__vTimeout__DOT__t_cnt;
    // Body
    __Vdly__vTimeout__DOT__t_cnt = vlTOPp->vTimeout__DOT__t_cnt;
    if (vlTOPp->reset) {
        vlTOPp->vTimeout__DOT__t = 0U;
        __Vdly__vTimeout__DOT__t_cnt = 0U;
    } else {
        if ((7U == (IData)(vlTOPp->vTimeout__DOT__t_cnt))) {
            vlTOPp->vTimeout__DOT__t = 1U;
        }
        if ((7U == (IData)(vlTOPp->vTimeout__DOT__t_cnt))) {
            __Vdly__vTimeout__DOT__t_cnt = 0U;
        }
        if ((7U != (IData)(vlTOPp->vTimeout__DOT__t_cnt))) {
            __Vdly__vTimeout__DOT__t_cnt = (7U & ((IData)(1U) 
                                                  + (IData)(vlTOPp->vTimeout__DOT__t_cnt)));
        }
    }
    vlTOPp->vTimeout__DOT__t_cnt = __Vdly__vTimeout__DOT__t_cnt;
    vlTOPp->ts = vlTOPp->vTimeout__DOT__t;
}

void VvTimeout::_eval(VvTimeout__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvTimeout::_eval\n"); );
    VvTimeout* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    if ((((IData)(vlTOPp->clk) & (~ (IData)(vlTOPp->__Vclklast__TOP__clk))) 
         | ((IData)(vlTOPp->reset) & (~ (IData)(vlTOPp->__Vclklast__TOP__reset))))) {
        vlTOPp->_sequent__TOP__1(vlSymsp);
    }
    // Final
    vlTOPp->__Vclklast__TOP__clk = vlTOPp->clk;
    vlTOPp->__Vclklast__TOP__reset = vlTOPp->reset;
}

VL_INLINE_OPT QData VvTimeout::_change_request(VvTimeout__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvTimeout::_change_request\n"); );
    VvTimeout* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    return (vlTOPp->_change_request_1(vlSymsp));
}

VL_INLINE_OPT QData VvTimeout::_change_request_1(VvTimeout__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvTimeout::_change_request_1\n"); );
    VvTimeout* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    // Change detection
    QData __req = false;  // Logically a bool
    return __req;
}

#ifdef VL_DEBUG
void VvTimeout::_eval_debug_assertions() {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvTimeout::_eval_debug_assertions\n"); );
    // Body
    if (VL_UNLIKELY((en & 0xfeU))) {
        Verilated::overWidthError("en");}
    if (VL_UNLIKELY((clk & 0xfeU))) {
        Verilated::overWidthError("clk");}
    if (VL_UNLIKELY((reset & 0xfeU))) {
        Verilated::overWidthError("reset");}
}
#endif  // VL_DEBUG
