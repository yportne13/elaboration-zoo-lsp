// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See VvPulseCC.h for the primary calling header

#include "VvPulseCC.h"
#include "VvPulseCC__Syms.h"

//==========

void VvPulseCC::eval_step() {
    VL_DEBUG_IF(VL_DBG_MSGF("+++++TOP Evaluate VvPulseCC::eval\n"); );
    VvPulseCC__Syms* __restrict vlSymsp = this->__VlSymsp;  // Setup global symbol table
    VvPulseCC* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
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
            VL_FATAL_MT("/mnt/f/projects/hermes/elaboration-zoo-lsp/tools/spinalhdl-verify/work/vPulseCC.v", 1, "",
                "Verilated model didn't converge\n"
                "- See DIDNOTCONVERGE in the Verilator manual");
        } else {
            __Vchange = _change_request(vlSymsp);
        }
    } while (VL_UNLIKELY(__Vchange));
}

void VvPulseCC::_eval_initial_loop(VvPulseCC__Syms* __restrict vlSymsp) {
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
            VL_FATAL_MT("/mnt/f/projects/hermes/elaboration-zoo-lsp/tools/spinalhdl-verify/work/vPulseCC.v", 1, "",
                "Verilated model didn't DC converge\n"
                "- See DIDNOTCONVERGE in the Verilator manual");
        } else {
            __Vchange = _change_request(vlSymsp);
        }
    } while (VL_UNLIKELY(__Vchange));
}

VL_INLINE_OPT void VvPulseCC::_sequent__TOP__1(VvPulseCC__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvPulseCC::_sequent__TOP__1\n"); );
    VvPulseCC* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    vlTOPp->__Vdly__vPulseCC__DOT_____05Ftoggle = vlTOPp->vPulseCC__DOT_____05Ftoggle;
    if (vlTOPp->pulseIn) {
        vlTOPp->__Vdly__vPulseCC__DOT_____05Ftoggle 
            = (1U & (~ (IData)(vlTOPp->vPulseCC__DOT_____05Ftoggle)));
    }
}

VL_INLINE_OPT void VvPulseCC::_sequent__TOP__2(VvPulseCC__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvPulseCC::_sequent__TOP__2\n"); );
    VvPulseCC* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    vlTOPp->vPulseCC__DOT_____05Fsync2 = vlTOPp->vPulseCC__DOT_____05Fsync1;
    vlTOPp->vPulseCC__DOT_____05Fsync1 = vlTOPp->vPulseCC__DOT_____05Ftoggle;
    vlTOPp->pulseOut = ((IData)(vlTOPp->vPulseCC__DOT_____05Fsync1) 
                        ^ (IData)(vlTOPp->vPulseCC__DOT_____05Fsync2));
}

VL_INLINE_OPT void VvPulseCC::_sequent__TOP__4(VvPulseCC__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvPulseCC::_sequent__TOP__4\n"); );
    VvPulseCC* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    vlTOPp->vPulseCC__DOT_____05Ftoggle = vlTOPp->__Vdly__vPulseCC__DOT_____05Ftoggle;
}

void VvPulseCC::_eval(VvPulseCC__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvPulseCC::_eval\n"); );
    VvPulseCC* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    if (((IData)(vlTOPp->clkA) & (~ (IData)(vlTOPp->__Vclklast__TOP__clkA)))) {
        vlTOPp->_sequent__TOP__1(vlSymsp);
    }
    if (((IData)(vlTOPp->clkB) & (~ (IData)(vlTOPp->__Vclklast__TOP__clkB)))) {
        vlTOPp->_sequent__TOP__2(vlSymsp);
    }
    if (((IData)(vlTOPp->clkA) & (~ (IData)(vlTOPp->__Vclklast__TOP__clkA)))) {
        vlTOPp->_sequent__TOP__4(vlSymsp);
    }
    // Final
    vlTOPp->__Vclklast__TOP__clkA = vlTOPp->clkA;
    vlTOPp->__Vclklast__TOP__clkB = vlTOPp->clkB;
}

VL_INLINE_OPT QData VvPulseCC::_change_request(VvPulseCC__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvPulseCC::_change_request\n"); );
    VvPulseCC* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    return (vlTOPp->_change_request_1(vlSymsp));
}

VL_INLINE_OPT QData VvPulseCC::_change_request_1(VvPulseCC__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvPulseCC::_change_request_1\n"); );
    VvPulseCC* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    // Change detection
    QData __req = false;  // Logically a bool
    return __req;
}

#ifdef VL_DEBUG
void VvPulseCC::_eval_debug_assertions() {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvPulseCC::_eval_debug_assertions\n"); );
    // Body
    if (VL_UNLIKELY((pulseIn & 0xfeU))) {
        Verilated::overWidthError("pulseIn");}
    if (VL_UNLIKELY((clkA & 0xfeU))) {
        Verilated::overWidthError("clkA");}
    if (VL_UNLIKELY((clkB & 0xfeU))) {
        Verilated::overWidthError("clkB");}
}
#endif  // VL_DEBUG
