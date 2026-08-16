// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See VvTimer.h for the primary calling header

#include "VvTimer.h"
#include "VvTimer__Syms.h"

//==========

void VvTimer::eval_step() {
    VL_DEBUG_IF(VL_DBG_MSGF("+++++TOP Evaluate VvTimer::eval\n"); );
    VvTimer__Syms* __restrict vlSymsp = this->__VlSymsp;  // Setup global symbol table
    VvTimer* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
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
            VL_FATAL_MT("/mnt/f/projects/hermes/elaboration-zoo-lsp/tools/spinalhdl-verify/work/vTimer.v", 1, "",
                "Verilated model didn't converge\n"
                "- See DIDNOTCONVERGE in the Verilator manual");
        } else {
            __Vchange = _change_request(vlSymsp);
        }
    } while (VL_UNLIKELY(__Vchange));
}

void VvTimer::_eval_initial_loop(VvTimer__Syms* __restrict vlSymsp) {
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
            VL_FATAL_MT("/mnt/f/projects/hermes/elaboration-zoo-lsp/tools/spinalhdl-verify/work/vTimer.v", 1, "",
                "Verilated model didn't DC converge\n"
                "- See DIDNOTCONVERGE in the Verilator manual");
        } else {
            __Vchange = _change_request(vlSymsp);
        }
    } while (VL_UNLIKELY(__Vchange));
}

VL_INLINE_OPT void VvTimer::_sequent__TOP__1(VvTimer__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvTimer::_sequent__TOP__1\n"); );
    VvTimer* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Variables
    CData/*7:0*/ __Vdly__vTimer__DOT__t_cnt;
    // Body
    __Vdly__vTimer__DOT__t_cnt = vlTOPp->vTimer__DOT__t_cnt;
    if (vlTOPp->reset) {
        __Vdly__vTimer__DOT__t_cnt = 0U;
        vlTOPp->vTimer__DOT__t_inhibit = 0U;
    } else {
        if (vlTOPp->tick) {
            vlTOPp->vTimer__DOT__t_inhibit = ((IData)(vlTOPp->vTimer__DOT__t_cnt) 
                                              == (IData)(vlTOPp->lim));
        }
        if (vlTOPp->tick) {
            __Vdly__vTimer__DOT__t_cnt = (0xffU & (
                                                   ((IData)(vlTOPp->vTimer__DOT__t_cnt) 
                                                    == (IData)(vlTOPp->lim))
                                                    ? (IData)(vlTOPp->vTimer__DOT__t_cnt)
                                                    : 
                                                   ((IData)(1U) 
                                                    + (IData)(vlTOPp->vTimer__DOT__t_cnt))));
        }
        if (vlTOPp->clr) {
            __Vdly__vTimer__DOT__t_cnt = 0U;
        }
        if (vlTOPp->clr) {
            vlTOPp->vTimer__DOT__t_inhibit = 0U;
        }
    }
    vlTOPp->vTimer__DOT__t_cnt = __Vdly__vTimer__DOT__t_cnt;
    vlTOPp->value = vlTOPp->vTimer__DOT__t_cnt;
}

VL_INLINE_OPT void VvTimer::_combo__TOP__3(VvTimer__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvTimer::_combo__TOP__3\n"); );
    VvTimer* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    vlTOPp->full = ((((IData)(vlTOPp->vTimer__DOT__t_cnt) 
                      == (IData)(vlTOPp->lim)) & (IData)(vlTOPp->tick)) 
                    & (~ (IData)(vlTOPp->vTimer__DOT__t_inhibit)));
}

void VvTimer::_eval(VvTimer__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvTimer::_eval\n"); );
    VvTimer* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    if ((((IData)(vlTOPp->clk) & (~ (IData)(vlTOPp->__Vclklast__TOP__clk))) 
         | ((IData)(vlTOPp->reset) & (~ (IData)(vlTOPp->__Vclklast__TOP__reset))))) {
        vlTOPp->_sequent__TOP__1(vlSymsp);
    }
    vlTOPp->_combo__TOP__3(vlSymsp);
    // Final
    vlTOPp->__Vclklast__TOP__clk = vlTOPp->clk;
    vlTOPp->__Vclklast__TOP__reset = vlTOPp->reset;
}

VL_INLINE_OPT QData VvTimer::_change_request(VvTimer__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvTimer::_change_request\n"); );
    VvTimer* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    return (vlTOPp->_change_request_1(vlSymsp));
}

VL_INLINE_OPT QData VvTimer::_change_request_1(VvTimer__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvTimer::_change_request_1\n"); );
    VvTimer* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    // Change detection
    QData __req = false;  // Logically a bool
    return __req;
}

#ifdef VL_DEBUG
void VvTimer::_eval_debug_assertions() {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvTimer::_eval_debug_assertions\n"); );
    // Body
    if (VL_UNLIKELY((tick & 0xfeU))) {
        Verilated::overWidthError("tick");}
    if (VL_UNLIKELY((clr & 0xfeU))) {
        Verilated::overWidthError("clr");}
    if (VL_UNLIKELY((clk & 0xfeU))) {
        Verilated::overWidthError("clk");}
    if (VL_UNLIKELY((reset & 0xfeU))) {
        Verilated::overWidthError("reset");}
}
#endif  // VL_DEBUG
