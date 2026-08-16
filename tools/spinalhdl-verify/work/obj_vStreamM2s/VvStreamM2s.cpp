// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See VvStreamM2s.h for the primary calling header

#include "VvStreamM2s.h"
#include "VvStreamM2s__Syms.h"

//==========

void VvStreamM2s::eval_step() {
    VL_DEBUG_IF(VL_DBG_MSGF("+++++TOP Evaluate VvStreamM2s::eval\n"); );
    VvStreamM2s__Syms* __restrict vlSymsp = this->__VlSymsp;  // Setup global symbol table
    VvStreamM2s* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
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
            VL_FATAL_MT("/mnt/f/projects/hermes/elaboration-zoo-lsp/tools/spinalhdl-verify/work/vStreamM2s.v", 1, "",
                "Verilated model didn't converge\n"
                "- See DIDNOTCONVERGE in the Verilator manual");
        } else {
            __Vchange = _change_request(vlSymsp);
        }
    } while (VL_UNLIKELY(__Vchange));
}

void VvStreamM2s::_eval_initial_loop(VvStreamM2s__Syms* __restrict vlSymsp) {
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
            VL_FATAL_MT("/mnt/f/projects/hermes/elaboration-zoo-lsp/tools/spinalhdl-verify/work/vStreamM2s.v", 1, "",
                "Verilated model didn't DC converge\n"
                "- See DIDNOTCONVERGE in the Verilator manual");
        } else {
            __Vchange = _change_request(vlSymsp);
        }
    } while (VL_UNLIKELY(__Vchange));
}

VL_INLINE_OPT void VvStreamM2s::_sequent__TOP__1(VvStreamM2s__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvStreamM2s::_sequent__TOP__1\n"); );
    VvStreamM2s* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    if ((1U & (~ (IData)(vlTOPp->reset)))) {
        if (vlTOPp->push_ready) {
            vlTOPp->vStreamM2s__DOT__piped_data = vlTOPp->push_payload;
        }
    }
    if (vlTOPp->reset) {
        vlTOPp->vStreamM2s__DOT__piped_valid = 0U;
    } else {
        if (vlTOPp->push_ready) {
            vlTOPp->vStreamM2s__DOT__piped_valid = vlTOPp->push_valid;
        }
    }
    vlTOPp->pop_payload = vlTOPp->vStreamM2s__DOT__piped_data;
    vlTOPp->pop_valid = vlTOPp->vStreamM2s__DOT__piped_valid;
}

VL_INLINE_OPT void VvStreamM2s::_combo__TOP__3(VvStreamM2s__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvStreamM2s::_combo__TOP__3\n"); );
    VvStreamM2s* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    vlTOPp->push_ready = ((IData)(vlTOPp->vStreamM2s__DOT__piped_valid) 
                          | (IData)(vlTOPp->pop_ready));
}

void VvStreamM2s::_eval(VvStreamM2s__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvStreamM2s::_eval\n"); );
    VvStreamM2s* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
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

VL_INLINE_OPT QData VvStreamM2s::_change_request(VvStreamM2s__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvStreamM2s::_change_request\n"); );
    VvStreamM2s* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    return (vlTOPp->_change_request_1(vlSymsp));
}

VL_INLINE_OPT QData VvStreamM2s::_change_request_1(VvStreamM2s__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvStreamM2s::_change_request_1\n"); );
    VvStreamM2s* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    // Change detection
    QData __req = false;  // Logically a bool
    return __req;
}

#ifdef VL_DEBUG
void VvStreamM2s::_eval_debug_assertions() {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvStreamM2s::_eval_debug_assertions\n"); );
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
