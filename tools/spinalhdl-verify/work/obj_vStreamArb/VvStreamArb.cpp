// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See VvStreamArb.h for the primary calling header

#include "VvStreamArb.h"
#include "VvStreamArb__Syms.h"

//==========

void VvStreamArb::eval_step() {
    VL_DEBUG_IF(VL_DBG_MSGF("+++++TOP Evaluate VvStreamArb::eval\n"); );
    VvStreamArb__Syms* __restrict vlSymsp = this->__VlSymsp;  // Setup global symbol table
    VvStreamArb* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
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
            VL_FATAL_MT("/mnt/f/projects/hermes/elaboration-zoo-lsp/tools/spinalhdl-verify/work/vStreamArb.v", 1, "",
                "Verilated model didn't converge\n"
                "- See DIDNOTCONVERGE in the Verilator manual");
        } else {
            __Vchange = _change_request(vlSymsp);
        }
    } while (VL_UNLIKELY(__Vchange));
}

void VvStreamArb::_eval_initial_loop(VvStreamArb__Syms* __restrict vlSymsp) {
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
            VL_FATAL_MT("/mnt/f/projects/hermes/elaboration-zoo-lsp/tools/spinalhdl-verify/work/vStreamArb.v", 1, "",
                "Verilated model didn't DC converge\n"
                "- See DIDNOTCONVERGE in the Verilator manual");
        } else {
            __Vchange = _change_request(vlSymsp);
        }
    } while (VL_UNLIKELY(__Vchange));
}

VL_INLINE_OPT void VvStreamArb::_combo__TOP__1(VvStreamArb__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvStreamArb::_combo__TOP__1\n"); );
    VvStreamArb* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    vlTOPp->a_ready = ((IData)(vlTOPp->a_valid) & (IData)(vlTOPp->m_ready));
    vlTOPp->m_valid = ((IData)(vlTOPp->a_valid) | (IData)(vlTOPp->b_valid));
    vlTOPp->b_ready = (((IData)(vlTOPp->b_valid) & 
                        (~ (IData)(vlTOPp->a_valid))) 
                       & (IData)(vlTOPp->m_ready));
    vlTOPp->m_payload = (0xffU & ((IData)(vlTOPp->a_valid)
                                   ? (IData)(vlTOPp->a_payload)
                                   : (((IData)(vlTOPp->b_valid) 
                                       & (~ (IData)(vlTOPp->a_valid)))
                                       ? (IData)(vlTOPp->b_payload)
                                       : 0U)));
}

void VvStreamArb::_eval(VvStreamArb__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvStreamArb::_eval\n"); );
    VvStreamArb* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    vlTOPp->_combo__TOP__1(vlSymsp);
}

VL_INLINE_OPT QData VvStreamArb::_change_request(VvStreamArb__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvStreamArb::_change_request\n"); );
    VvStreamArb* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    return (vlTOPp->_change_request_1(vlSymsp));
}

VL_INLINE_OPT QData VvStreamArb::_change_request_1(VvStreamArb__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvStreamArb::_change_request_1\n"); );
    VvStreamArb* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    // Change detection
    QData __req = false;  // Logically a bool
    return __req;
}

#ifdef VL_DEBUG
void VvStreamArb::_eval_debug_assertions() {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvStreamArb::_eval_debug_assertions\n"); );
    // Body
    if (VL_UNLIKELY((a_valid & 0xfeU))) {
        Verilated::overWidthError("a_valid");}
    if (VL_UNLIKELY((b_valid & 0xfeU))) {
        Verilated::overWidthError("b_valid");}
    if (VL_UNLIKELY((m_ready & 0xfeU))) {
        Verilated::overWidthError("m_ready");}
}
#endif  // VL_DEBUG
