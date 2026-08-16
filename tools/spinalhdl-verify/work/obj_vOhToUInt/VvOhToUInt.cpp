// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See VvOhToUInt.h for the primary calling header

#include "VvOhToUInt.h"
#include "VvOhToUInt__Syms.h"

//==========

void VvOhToUInt::eval_step() {
    VL_DEBUG_IF(VL_DBG_MSGF("+++++TOP Evaluate VvOhToUInt::eval\n"); );
    VvOhToUInt__Syms* __restrict vlSymsp = this->__VlSymsp;  // Setup global symbol table
    VvOhToUInt* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
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
            VL_FATAL_MT("/mnt/f/projects/hermes/elaboration-zoo-lsp/tools/spinalhdl-verify/work/vOhToUInt.v", 1, "",
                "Verilated model didn't converge\n"
                "- See DIDNOTCONVERGE in the Verilator manual");
        } else {
            __Vchange = _change_request(vlSymsp);
        }
    } while (VL_UNLIKELY(__Vchange));
}

void VvOhToUInt::_eval_initial_loop(VvOhToUInt__Syms* __restrict vlSymsp) {
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
            VL_FATAL_MT("/mnt/f/projects/hermes/elaboration-zoo-lsp/tools/spinalhdl-verify/work/vOhToUInt.v", 1, "",
                "Verilated model didn't DC converge\n"
                "- See DIDNOTCONVERGE in the Verilator manual");
        } else {
            __Vchange = _change_request(vlSymsp);
        }
    } while (VL_UNLIKELY(__Vchange));
}

VL_INLINE_OPT void VvOhToUInt::_combo__TOP__1(VvOhToUInt__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvOhToUInt::_combo__TOP__1\n"); );
    VvOhToUInt* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    vlTOPp->idx = ((4U & ((0x3ffffffcU & ((IData)(vlTOPp->oh) 
                                          >> 2U)) | 
                          ((0x1ffffffcU & ((IData)(vlTOPp->oh) 
                                           >> 3U)) 
                           | ((0xffffffcU & ((IData)(vlTOPp->oh) 
                                             >> 4U)) 
                              | (0x7fffffcU & ((IData)(vlTOPp->oh) 
                                               >> 5U)))))) 
                   | ((2U & ((0x7ffffffeU & ((IData)(vlTOPp->oh) 
                                             >> 1U)) 
                             | ((0x3ffffffeU & ((IData)(vlTOPp->oh) 
                                                >> 2U)) 
                                | ((0x7fffffeU & ((IData)(vlTOPp->oh) 
                                                  >> 5U)) 
                                   | (0x3fffffeU & 
                                      ((IData)(vlTOPp->oh) 
                                       >> 6U)))))) 
                      | (1U & (((IData)(vlTOPp->oh) 
                                >> 1U) | (((IData)(vlTOPp->oh) 
                                           >> 3U) | 
                                          (((IData)(vlTOPp->oh) 
                                            >> 5U) 
                                           | ((IData)(vlTOPp->oh) 
                                              >> 7U)))))));
}

void VvOhToUInt::_eval(VvOhToUInt__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvOhToUInt::_eval\n"); );
    VvOhToUInt* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    vlTOPp->_combo__TOP__1(vlSymsp);
}

VL_INLINE_OPT QData VvOhToUInt::_change_request(VvOhToUInt__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvOhToUInt::_change_request\n"); );
    VvOhToUInt* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    return (vlTOPp->_change_request_1(vlSymsp));
}

VL_INLINE_OPT QData VvOhToUInt::_change_request_1(VvOhToUInt__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvOhToUInt::_change_request_1\n"); );
    VvOhToUInt* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    // Change detection
    QData __req = false;  // Logically a bool
    return __req;
}

#ifdef VL_DEBUG
void VvOhToUInt::_eval_debug_assertions() {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvOhToUInt::_eval_debug_assertions\n"); );
}
#endif  // VL_DEBUG
