// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See VvCounterUpDown.h for the primary calling header

#include "VvCounterUpDown.h"
#include "VvCounterUpDown__Syms.h"

//==========

void VvCounterUpDown::eval_step() {
    VL_DEBUG_IF(VL_DBG_MSGF("+++++TOP Evaluate VvCounterUpDown::eval\n"); );
    VvCounterUpDown__Syms* __restrict vlSymsp = this->__VlSymsp;  // Setup global symbol table
    VvCounterUpDown* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
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
            VL_FATAL_MT("/mnt/f/projects/hermes/elaboration-zoo-lsp/tools/spinalhdl-verify/work/vCounterUpDown.v", 1, "",
                "Verilated model didn't converge\n"
                "- See DIDNOTCONVERGE in the Verilator manual");
        } else {
            __Vchange = _change_request(vlSymsp);
        }
    } while (VL_UNLIKELY(__Vchange));
}

void VvCounterUpDown::_eval_initial_loop(VvCounterUpDown__Syms* __restrict vlSymsp) {
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
            VL_FATAL_MT("/mnt/f/projects/hermes/elaboration-zoo-lsp/tools/spinalhdl-verify/work/vCounterUpDown.v", 1, "",
                "Verilated model didn't DC converge\n"
                "- See DIDNOTCONVERGE in the Verilator manual");
        } else {
            __Vchange = _change_request(vlSymsp);
        }
    } while (VL_UNLIKELY(__Vchange));
}

VL_INLINE_OPT void VvCounterUpDown::_sequent__TOP__1(VvCounterUpDown__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvCounterUpDown::_sequent__TOP__1\n"); );
    VvCounterUpDown* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Variables
    CData/*6:0*/ __Vtableidx1;
    // Body
    __Vtableidx1 = (((IData)(vlTOPp->vCounterUpDown__DOT__ud) 
                     << 3U) | (((IData)(vlTOPp->dec) 
                                << 2U) | (((IData)(vlTOPp->inc) 
                                           << 1U) | (IData)(vlTOPp->reset))));
    if (vlTOPp->__Vtablechg1[__Vtableidx1]) {
        vlTOPp->vCounterUpDown__DOT__ud = vlTOPp->__Vtable1_vCounterUpDown__DOT__ud
            [__Vtableidx1];
    }
    vlTOPp->value = vlTOPp->vCounterUpDown__DOT__ud;
    vlTOPp->willOverflowIfInc = (9U == (IData)(vlTOPp->vCounterUpDown__DOT__ud));
    vlTOPp->willUnderflowIfDec = (0U == (IData)(vlTOPp->vCounterUpDown__DOT__ud));
}

VL_INLINE_OPT void VvCounterUpDown::_combo__TOP__3(VvCounterUpDown__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvCounterUpDown::_combo__TOP__3\n"); );
    VvCounterUpDown* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    vlTOPp->willOverflow = (((IData)(vlTOPp->inc) & 
                             (~ (IData)(vlTOPp->dec))) 
                            & (9U == (IData)(vlTOPp->vCounterUpDown__DOT__ud)));
    vlTOPp->willUnderflow = (((IData)(vlTOPp->dec) 
                              & (~ (IData)(vlTOPp->inc))) 
                             & (0U == (IData)(vlTOPp->vCounterUpDown__DOT__ud)));
}

void VvCounterUpDown::_eval(VvCounterUpDown__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvCounterUpDown::_eval\n"); );
    VvCounterUpDown* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
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

VL_INLINE_OPT QData VvCounterUpDown::_change_request(VvCounterUpDown__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvCounterUpDown::_change_request\n"); );
    VvCounterUpDown* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    return (vlTOPp->_change_request_1(vlSymsp));
}

VL_INLINE_OPT QData VvCounterUpDown::_change_request_1(VvCounterUpDown__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvCounterUpDown::_change_request_1\n"); );
    VvCounterUpDown* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    // Change detection
    QData __req = false;  // Logically a bool
    return __req;
}

#ifdef VL_DEBUG
void VvCounterUpDown::_eval_debug_assertions() {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvCounterUpDown::_eval_debug_assertions\n"); );
    // Body
    if (VL_UNLIKELY((inc & 0xfeU))) {
        Verilated::overWidthError("inc");}
    if (VL_UNLIKELY((dec & 0xfeU))) {
        Verilated::overWidthError("dec");}
    if (VL_UNLIKELY((clk & 0xfeU))) {
        Verilated::overWidthError("clk");}
    if (VL_UNLIKELY((reset & 0xfeU))) {
        Verilated::overWidthError("reset");}
}
#endif  // VL_DEBUG
