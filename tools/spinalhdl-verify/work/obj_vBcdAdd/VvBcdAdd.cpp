// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See VvBcdAdd.h for the primary calling header

#include "VvBcdAdd.h"
#include "VvBcdAdd__Syms.h"

//==========

void VvBcdAdd::eval_step() {
    VL_DEBUG_IF(VL_DBG_MSGF("+++++TOP Evaluate VvBcdAdd::eval\n"); );
    VvBcdAdd__Syms* __restrict vlSymsp = this->__VlSymsp;  // Setup global symbol table
    VvBcdAdd* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
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
            VL_FATAL_MT("/mnt/f/projects/hermes/elaboration-zoo-lsp/tools/spinalhdl-verify/work/vBcdAdd.v", 1, "",
                "Verilated model didn't converge\n"
                "- See DIDNOTCONVERGE in the Verilator manual");
        } else {
            __Vchange = _change_request(vlSymsp);
        }
    } while (VL_UNLIKELY(__Vchange));
}

void VvBcdAdd::_eval_initial_loop(VvBcdAdd__Syms* __restrict vlSymsp) {
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
            VL_FATAL_MT("/mnt/f/projects/hermes/elaboration-zoo-lsp/tools/spinalhdl-verify/work/vBcdAdd.v", 1, "",
                "Verilated model didn't DC converge\n"
                "- See DIDNOTCONVERGE in the Verilator manual");
        } else {
            __Vchange = _change_request(vlSymsp);
        }
    } while (VL_UNLIKELY(__Vchange));
}

VL_INLINE_OPT void VvBcdAdd::_combo__TOP__1(VvBcdAdd__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvBcdAdd::_combo__TOP__1\n"); );
    VvBcdAdd* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    vlTOPp->s = (0xfU & ((((IData)(vlTOPp->a) + (IData)(vlTOPp->b)) 
                          + ((IData)(vlTOPp->cin) ? 1U
                              : 0U)) + ((9U < (((IData)(vlTOPp->a) 
                                                + (IData)(vlTOPp->b)) 
                                               + ((IData)(vlTOPp->cin)
                                                   ? 1U
                                                   : 0U)))
                                         ? 6U : 0U)));
    vlTOPp->co = (9U < (((IData)(vlTOPp->a) + (IData)(vlTOPp->b)) 
                        + ((IData)(vlTOPp->cin) ? 1U
                            : 0U)));
}

void VvBcdAdd::_eval(VvBcdAdd__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvBcdAdd::_eval\n"); );
    VvBcdAdd* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    vlTOPp->_combo__TOP__1(vlSymsp);
}

VL_INLINE_OPT QData VvBcdAdd::_change_request(VvBcdAdd__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvBcdAdd::_change_request\n"); );
    VvBcdAdd* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    return (vlTOPp->_change_request_1(vlSymsp));
}

VL_INLINE_OPT QData VvBcdAdd::_change_request_1(VvBcdAdd__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvBcdAdd::_change_request_1\n"); );
    VvBcdAdd* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    // Change detection
    QData __req = false;  // Logically a bool
    return __req;
}

#ifdef VL_DEBUG
void VvBcdAdd::_eval_debug_assertions() {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvBcdAdd::_eval_debug_assertions\n"); );
    // Body
    if (VL_UNLIKELY((a & 0xf0U))) {
        Verilated::overWidthError("a");}
    if (VL_UNLIKELY((b & 0xf0U))) {
        Verilated::overWidthError("b");}
    if (VL_UNLIKELY((cin & 0xfeU))) {
        Verilated::overWidthError("cin");}
}
#endif  // VL_DEBUG
