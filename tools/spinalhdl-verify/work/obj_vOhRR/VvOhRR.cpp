// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See VvOhRR.h for the primary calling header

#include "VvOhRR.h"
#include "VvOhRR__Syms.h"

//==========

void VvOhRR::eval_step() {
    VL_DEBUG_IF(VL_DBG_MSGF("+++++TOP Evaluate VvOhRR::eval\n"); );
    VvOhRR__Syms* __restrict vlSymsp = this->__VlSymsp;  // Setup global symbol table
    VvOhRR* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
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
            VL_FATAL_MT("/mnt/f/projects/hermes/elaboration-zoo-lsp/tools/spinalhdl-verify/work/vOhRR.v", 1, "",
                "Verilated model didn't converge\n"
                "- See DIDNOTCONVERGE in the Verilator manual");
        } else {
            __Vchange = _change_request(vlSymsp);
        }
    } while (VL_UNLIKELY(__Vchange));
}

void VvOhRR::_eval_initial_loop(VvOhRR__Syms* __restrict vlSymsp) {
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
            VL_FATAL_MT("/mnt/f/projects/hermes/elaboration-zoo-lsp/tools/spinalhdl-verify/work/vOhRR.v", 1, "",
                "Verilated model didn't DC converge\n"
                "- See DIDNOTCONVERGE in the Verilator manual");
        } else {
            __Vchange = _change_request(vlSymsp);
        }
    } while (VL_UNLIKELY(__Vchange));
}

VL_INLINE_OPT void VvOhRR::_combo__TOP__1(VvOhRR__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvOhRR::_combo__TOP__1\n"); );
    VvOhRR* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    vlTOPp->g = (0xfU & ((0xffU & ((((IData)(vlTOPp->req) 
                                     << 4U) | (IData)(vlTOPp->req)) 
                                   & (~ ((0xffU & (
                                                   ((IData)(vlTOPp->req) 
                                                    << 4U) 
                                                   | (IData)(vlTOPp->req))) 
                                         - (IData)(vlTOPp->pri))))) 
                         | (0xfU & (((0xfffffffU & (IData)(vlTOPp->req)) 
                                     | ((IData)(vlTOPp->req) 
                                        >> 4U)) & (
                                                   (~ 
                                                    ((0xffU 
                                                      & (((IData)(vlTOPp->req) 
                                                          << 4U) 
                                                         | (IData)(vlTOPp->req))) 
                                                     - (IData)(vlTOPp->pri))) 
                                                   >> 4U)))));
}

void VvOhRR::_eval(VvOhRR__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvOhRR::_eval\n"); );
    VvOhRR* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    vlTOPp->_combo__TOP__1(vlSymsp);
}

VL_INLINE_OPT QData VvOhRR::_change_request(VvOhRR__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvOhRR::_change_request\n"); );
    VvOhRR* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    return (vlTOPp->_change_request_1(vlSymsp));
}

VL_INLINE_OPT QData VvOhRR::_change_request_1(VvOhRR__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvOhRR::_change_request_1\n"); );
    VvOhRR* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    // Change detection
    QData __req = false;  // Logically a bool
    return __req;
}

#ifdef VL_DEBUG
void VvOhRR::_eval_debug_assertions() {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvOhRR::_eval_debug_assertions\n"); );
    // Body
    if (VL_UNLIKELY((req & 0xf0U))) {
        Verilated::overWidthError("req");}
    if (VL_UNLIKELY((pri & 0xf0U))) {
        Verilated::overWidthError("pri");}
}
#endif  // VL_DEBUG
