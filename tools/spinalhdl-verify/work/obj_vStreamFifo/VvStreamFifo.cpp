// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See VvStreamFifo.h for the primary calling header

#include "VvStreamFifo.h"
#include "VvStreamFifo__Syms.h"

//==========

void VvStreamFifo::eval_step() {
    VL_DEBUG_IF(VL_DBG_MSGF("+++++TOP Evaluate VvStreamFifo::eval\n"); );
    VvStreamFifo__Syms* __restrict vlSymsp = this->__VlSymsp;  // Setup global symbol table
    VvStreamFifo* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
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
            VL_FATAL_MT("/mnt/f/projects/hermes/elaboration-zoo-lsp/tools/spinalhdl-verify/work/vStreamFifo.v", 1, "",
                "Verilated model didn't converge\n"
                "- See DIDNOTCONVERGE in the Verilator manual");
        } else {
            __Vchange = _change_request(vlSymsp);
        }
    } while (VL_UNLIKELY(__Vchange));
}

void VvStreamFifo::_eval_initial_loop(VvStreamFifo__Syms* __restrict vlSymsp) {
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
            VL_FATAL_MT("/mnt/f/projects/hermes/elaboration-zoo-lsp/tools/spinalhdl-verify/work/vStreamFifo.v", 1, "",
                "Verilated model didn't DC converge\n"
                "- See DIDNOTCONVERGE in the Verilator manual");
        } else {
            __Vchange = _change_request(vlSymsp);
        }
    } while (VL_UNLIKELY(__Vchange));
}

VL_INLINE_OPT void VvStreamFifo::_sequent__TOP__1(VvStreamFifo__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvStreamFifo::_sequent__TOP__1\n"); );
    VvStreamFifo* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Variables
    CData/*2:0*/ __Vdly__vStreamFifo__DOT__fifo_ptrPush;
    CData/*1:0*/ __Vdlyvdim0__vStreamFifo__DOT__fifo_mem__v0;
    CData/*7:0*/ __Vdlyvval__vStreamFifo__DOT__fifo_mem__v0;
    CData/*0:0*/ __Vdlyvset__vStreamFifo__DOT__fifo_mem__v0;
    CData/*2:0*/ __Vdly__vStreamFifo__DOT__fifo_ptrPop;
    // Body
    __Vdlyvset__vStreamFifo__DOT__fifo_mem__v0 = 0U;
    __Vdly__vStreamFifo__DOT__fifo_ptrPop = vlTOPp->vStreamFifo__DOT__fifo_ptrPop;
    __Vdly__vStreamFifo__DOT__fifo_ptrPush = vlTOPp->vStreamFifo__DOT__fifo_ptrPush;
    if (vlTOPp->reset) {
        __Vdly__vStreamFifo__DOT__fifo_ptrPop = 0U;
    } else {
        if (((IData)(vlTOPp->vStreamFifo__DOT__fifo_pop_valid) 
             & (IData)(vlTOPp->pop_ready))) {
            __Vdly__vStreamFifo__DOT__fifo_ptrPop = 
                (7U & ((IData)(1U) + (IData)(vlTOPp->vStreamFifo__DOT__fifo_ptrPop)));
        }
    }
    if (vlTOPp->reset) {
        __Vdly__vStreamFifo__DOT__fifo_ptrPush = 0U;
    } else {
        if (((IData)(vlTOPp->push_valid) & (IData)(vlTOPp->vStreamFifo__DOT__fifo_push_ready))) {
            __Vdlyvval__vStreamFifo__DOT__fifo_mem__v0 
                = vlTOPp->push_payload;
            __Vdlyvset__vStreamFifo__DOT__fifo_mem__v0 = 1U;
            __Vdlyvdim0__vStreamFifo__DOT__fifo_mem__v0 
                = (3U & (IData)(vlTOPp->vStreamFifo__DOT__fifo_ptrPush));
        }
        if (((IData)(vlTOPp->push_valid) & (IData)(vlTOPp->vStreamFifo__DOT__fifo_push_ready))) {
            __Vdly__vStreamFifo__DOT__fifo_ptrPush 
                = (7U & ((IData)(1U) + (IData)(vlTOPp->vStreamFifo__DOT__fifo_ptrPush)));
        }
    }
    vlTOPp->vStreamFifo__DOT__fifo_ptrPop = __Vdly__vStreamFifo__DOT__fifo_ptrPop;
    if (__Vdlyvset__vStreamFifo__DOT__fifo_mem__v0) {
        vlTOPp->vStreamFifo__DOT__fifo_mem[__Vdlyvdim0__vStreamFifo__DOT__fifo_mem__v0] 
            = __Vdlyvval__vStreamFifo__DOT__fifo_mem__v0;
    }
    vlTOPp->vStreamFifo__DOT__fifo_ptrPush = __Vdly__vStreamFifo__DOT__fifo_ptrPush;
    vlTOPp->pop_payload = vlTOPp->vStreamFifo__DOT__fifo_mem
        [(3U & (IData)(vlTOPp->vStreamFifo__DOT__fifo_ptrPop))];
    vlTOPp->occ = (7U & ((IData)(vlTOPp->vStreamFifo__DOT__fifo_ptrPush) 
                         - (IData)(vlTOPp->vStreamFifo__DOT__fifo_ptrPop)));
    vlTOPp->vStreamFifo__DOT__fifo_push_ready = (4U 
                                                 != 
                                                 ((IData)(vlTOPp->vStreamFifo__DOT__fifo_ptrPush) 
                                                  ^ (IData)(vlTOPp->vStreamFifo__DOT__fifo_ptrPop)));
    vlTOPp->vStreamFifo__DOT__fifo_pop_valid = ((IData)(vlTOPp->vStreamFifo__DOT__fifo_ptrPush) 
                                                != (IData)(vlTOPp->vStreamFifo__DOT__fifo_ptrPop));
    vlTOPp->push_ready = vlTOPp->vStreamFifo__DOT__fifo_push_ready;
    vlTOPp->pop_valid = vlTOPp->vStreamFifo__DOT__fifo_pop_valid;
}

void VvStreamFifo::_eval(VvStreamFifo__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvStreamFifo::_eval\n"); );
    VvStreamFifo* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    if ((((IData)(vlTOPp->clk) & (~ (IData)(vlTOPp->__Vclklast__TOP__clk))) 
         | ((IData)(vlTOPp->reset) & (~ (IData)(vlTOPp->__Vclklast__TOP__reset))))) {
        vlTOPp->_sequent__TOP__1(vlSymsp);
    }
    // Final
    vlTOPp->__Vclklast__TOP__clk = vlTOPp->clk;
    vlTOPp->__Vclklast__TOP__reset = vlTOPp->reset;
}

VL_INLINE_OPT QData VvStreamFifo::_change_request(VvStreamFifo__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvStreamFifo::_change_request\n"); );
    VvStreamFifo* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    return (vlTOPp->_change_request_1(vlSymsp));
}

VL_INLINE_OPT QData VvStreamFifo::_change_request_1(VvStreamFifo__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvStreamFifo::_change_request_1\n"); );
    VvStreamFifo* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    // Change detection
    QData __req = false;  // Logically a bool
    return __req;
}

#ifdef VL_DEBUG
void VvStreamFifo::_eval_debug_assertions() {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvStreamFifo::_eval_debug_assertions\n"); );
    // Body
    if (VL_UNLIKELY((push_valid & 0xfeU))) {
        Verilated::overWidthError("push_valid");}
    if (VL_UNLIKELY((pop_ready & 0xfeU))) {
        Verilated::overWidthError("pop_ready");}
    if (VL_UNLIKELY((clk & 0xfeU))) {
        Verilated::overWidthError("clk");}
    if (VL_UNLIKELY((reset & 0xfeU))) {
        Verilated::overWidthError("reset");}
}
#endif  // VL_DEBUG
