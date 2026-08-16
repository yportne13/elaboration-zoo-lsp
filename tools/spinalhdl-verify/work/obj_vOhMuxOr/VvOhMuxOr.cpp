// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See VvOhMuxOr.h for the primary calling header

#include "VvOhMuxOr.h"
#include "VvOhMuxOr__Syms.h"

//==========

void VvOhMuxOr::eval_step() {
    VL_DEBUG_IF(VL_DBG_MSGF("+++++TOP Evaluate VvOhMuxOr::eval\n"); );
    VvOhMuxOr__Syms* __restrict vlSymsp = this->__VlSymsp;  // Setup global symbol table
    VvOhMuxOr* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
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
            VL_FATAL_MT("/mnt/f/projects/hermes/elaboration-zoo-lsp/tools/spinalhdl-verify/work/vOhMuxOr.v", 1, "",
                "Verilated model didn't converge\n"
                "- See DIDNOTCONVERGE in the Verilator manual");
        } else {
            __Vchange = _change_request(vlSymsp);
        }
    } while (VL_UNLIKELY(__Vchange));
}

void VvOhMuxOr::_eval_initial_loop(VvOhMuxOr__Syms* __restrict vlSymsp) {
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
            VL_FATAL_MT("/mnt/f/projects/hermes/elaboration-zoo-lsp/tools/spinalhdl-verify/work/vOhMuxOr.v", 1, "",
                "Verilated model didn't DC converge\n"
                "- See DIDNOTCONVERGE in the Verilator manual");
        } else {
            __Vchange = _change_request(vlSymsp);
        }
    } while (VL_UNLIKELY(__Vchange));
}

VL_INLINE_OPT void VvOhMuxOr::_combo__TOP__1(VvOhMuxOr__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvOhMuxOr::_combo__TOP__1\n"); );
    VvOhMuxOr* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    vlTOPp->o = (0xffU & (((1U & (IData)(vlTOPp->sel))
                            ? (IData)(vlTOPp->a) : 0U) 
                          | (((2U & (IData)(vlTOPp->sel))
                               ? (IData)(vlTOPp->b)
                               : 0U) | (((4U & (IData)(vlTOPp->sel))
                                          ? (IData)(vlTOPp->c)
                                          : 0U) | (
                                                   (8U 
                                                    & (IData)(vlTOPp->sel))
                                                    ? (IData)(vlTOPp->d)
                                                    : 0U)))));
}

void VvOhMuxOr::_eval(VvOhMuxOr__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvOhMuxOr::_eval\n"); );
    VvOhMuxOr* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    vlTOPp->_combo__TOP__1(vlSymsp);
}

VL_INLINE_OPT QData VvOhMuxOr::_change_request(VvOhMuxOr__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvOhMuxOr::_change_request\n"); );
    VvOhMuxOr* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    return (vlTOPp->_change_request_1(vlSymsp));
}

VL_INLINE_OPT QData VvOhMuxOr::_change_request_1(VvOhMuxOr__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvOhMuxOr::_change_request_1\n"); );
    VvOhMuxOr* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    // Change detection
    QData __req = false;  // Logically a bool
    return __req;
}

#ifdef VL_DEBUG
void VvOhMuxOr::_eval_debug_assertions() {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvOhMuxOr::_eval_debug_assertions\n"); );
    // Body
    if (VL_UNLIKELY((sel & 0xf0U))) {
        Verilated::overWidthError("sel");}
}
#endif  // VL_DEBUG
