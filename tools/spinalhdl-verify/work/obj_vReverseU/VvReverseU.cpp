// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See VvReverseU.h for the primary calling header

#include "VvReverseU.h"
#include "VvReverseU__Syms.h"

//==========

void VvReverseU::eval_step() {
    VL_DEBUG_IF(VL_DBG_MSGF("+++++TOP Evaluate VvReverseU::eval\n"); );
    VvReverseU__Syms* __restrict vlSymsp = this->__VlSymsp;  // Setup global symbol table
    VvReverseU* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
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
            VL_FATAL_MT("/mnt/f/projects/hermes/elaboration-zoo-lsp/tools/spinalhdl-verify/work/vReverseU.v", 1, "",
                "Verilated model didn't converge\n"
                "- See DIDNOTCONVERGE in the Verilator manual");
        } else {
            __Vchange = _change_request(vlSymsp);
        }
    } while (VL_UNLIKELY(__Vchange));
}

void VvReverseU::_eval_initial_loop(VvReverseU__Syms* __restrict vlSymsp) {
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
            VL_FATAL_MT("/mnt/f/projects/hermes/elaboration-zoo-lsp/tools/spinalhdl-verify/work/vReverseU.v", 1, "",
                "Verilated model didn't DC converge\n"
                "- See DIDNOTCONVERGE in the Verilator manual");
        } else {
            __Vchange = _change_request(vlSymsp);
        }
    } while (VL_UNLIKELY(__Vchange));
}

VL_INLINE_OPT void VvReverseU::_combo__TOP__1(VvReverseU__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvReverseU::_combo__TOP__1\n"); );
    VvReverseU* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    vlTOPp->r = ((0x80U & ((IData)(vlTOPp->a) << 7U)) 
                 | ((0x40U & ((IData)(vlTOPp->a) << 5U)) 
                    | ((0x20U & ((IData)(vlTOPp->a) 
                                 << 3U)) | ((0x10U 
                                             & ((IData)(vlTOPp->a) 
                                                << 1U)) 
                                            | ((8U 
                                                & ((IData)(vlTOPp->a) 
                                                   >> 1U)) 
                                               | ((4U 
                                                   & ((IData)(vlTOPp->a) 
                                                      >> 3U)) 
                                                  | ((2U 
                                                      & ((IData)(vlTOPp->a) 
                                                         >> 5U)) 
                                                     | (1U 
                                                        & ((IData)(vlTOPp->a) 
                                                           >> 7U)))))))));
}

void VvReverseU::_eval(VvReverseU__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvReverseU::_eval\n"); );
    VvReverseU* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    vlTOPp->_combo__TOP__1(vlSymsp);
}

VL_INLINE_OPT QData VvReverseU::_change_request(VvReverseU__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvReverseU::_change_request\n"); );
    VvReverseU* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    return (vlTOPp->_change_request_1(vlSymsp));
}

VL_INLINE_OPT QData VvReverseU::_change_request_1(VvReverseU__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvReverseU::_change_request_1\n"); );
    VvReverseU* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    // Change detection
    QData __req = false;  // Logically a bool
    return __req;
}

#ifdef VL_DEBUG
void VvReverseU::_eval_debug_assertions() {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvReverseU::_eval_debug_assertions\n"); );
}
#endif  // VL_DEBUG
