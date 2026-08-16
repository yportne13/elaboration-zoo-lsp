// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See VvCountOneOnEach.h for the primary calling header

#include "VvCountOneOnEach.h"
#include "VvCountOneOnEach__Syms.h"

//==========

void VvCountOneOnEach::eval_step() {
    VL_DEBUG_IF(VL_DBG_MSGF("+++++TOP Evaluate VvCountOneOnEach::eval\n"); );
    VvCountOneOnEach__Syms* __restrict vlSymsp = this->__VlSymsp;  // Setup global symbol table
    VvCountOneOnEach* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
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
            VL_FATAL_MT("/mnt/f/projects/hermes/elaboration-zoo-lsp/tools/spinalhdl-verify/work/vCountOneOnEach.v", 1, "",
                "Verilated model didn't converge\n"
                "- See DIDNOTCONVERGE in the Verilator manual");
        } else {
            __Vchange = _change_request(vlSymsp);
        }
    } while (VL_UNLIKELY(__Vchange));
}

void VvCountOneOnEach::_eval_initial_loop(VvCountOneOnEach__Syms* __restrict vlSymsp) {
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
            VL_FATAL_MT("/mnt/f/projects/hermes/elaboration-zoo-lsp/tools/spinalhdl-verify/work/vCountOneOnEach.v", 1, "",
                "Verilated model didn't DC converge\n"
                "- See DIDNOTCONVERGE in the Verilator manual");
        } else {
            __Vchange = _change_request(vlSymsp);
        }
    } while (VL_UNLIKELY(__Vchange));
}

VL_INLINE_OPT void VvCountOneOnEach::_combo__TOP__1(VvCountOneOnEach__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvCountOneOnEach::_combo__TOP__1\n"); );
    VvCountOneOnEach* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    vlTOPp->c1 = (1U & (IData)(vlTOPp->a));
    vlTOPp->c2 = (7U & ((1U & (IData)(vlTOPp->a)) + 
                        (1U & ((IData)(vlTOPp->a) >> 1U))));
    vlTOPp->c3 = (7U & ((3U & ((1U & (IData)(vlTOPp->a)) 
                               + (1U & ((IData)(vlTOPp->a) 
                                        >> 1U)))) + 
                        (1U & ((IData)(vlTOPp->a) >> 2U))));
    vlTOPp->c4 = (7U & ((3U & ((1U & (IData)(vlTOPp->a)) 
                               + (1U & ((IData)(vlTOPp->a) 
                                        >> 1U)))) + 
                        ((1U & ((IData)(vlTOPp->a) 
                                >> 2U)) + (1U & ((IData)(vlTOPp->a) 
                                                 >> 3U)))));
}

void VvCountOneOnEach::_eval(VvCountOneOnEach__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvCountOneOnEach::_eval\n"); );
    VvCountOneOnEach* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    vlTOPp->_combo__TOP__1(vlSymsp);
}

VL_INLINE_OPT QData VvCountOneOnEach::_change_request(VvCountOneOnEach__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvCountOneOnEach::_change_request\n"); );
    VvCountOneOnEach* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    return (vlTOPp->_change_request_1(vlSymsp));
}

VL_INLINE_OPT QData VvCountOneOnEach::_change_request_1(VvCountOneOnEach__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvCountOneOnEach::_change_request_1\n"); );
    VvCountOneOnEach* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    // Change detection
    QData __req = false;  // Logically a bool
    return __req;
}

#ifdef VL_DEBUG
void VvCountOneOnEach::_eval_debug_assertions() {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvCountOneOnEach::_eval_debug_assertions\n"); );
    // Body
    if (VL_UNLIKELY((a & 0xf0U))) {
        Verilated::overWidthError("a");}
}
#endif  // VL_DEBUG
