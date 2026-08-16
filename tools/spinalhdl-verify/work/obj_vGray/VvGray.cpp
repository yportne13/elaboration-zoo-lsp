// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See VvGray.h for the primary calling header

#include "VvGray.h"
#include "VvGray__Syms.h"

//==========

void VvGray::eval_step() {
    VL_DEBUG_IF(VL_DBG_MSGF("+++++TOP Evaluate VvGray::eval\n"); );
    VvGray__Syms* __restrict vlSymsp = this->__VlSymsp;  // Setup global symbol table
    VvGray* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
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
            VL_FATAL_MT("/mnt/f/projects/hermes/elaboration-zoo-lsp/tools/spinalhdl-verify/work/vGray.v", 1, "",
                "Verilated model didn't converge\n"
                "- See DIDNOTCONVERGE in the Verilator manual");
        } else {
            __Vchange = _change_request(vlSymsp);
        }
    } while (VL_UNLIKELY(__Vchange));
}

void VvGray::_eval_initial_loop(VvGray__Syms* __restrict vlSymsp) {
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
            VL_FATAL_MT("/mnt/f/projects/hermes/elaboration-zoo-lsp/tools/spinalhdl-verify/work/vGray.v", 1, "",
                "Verilated model didn't DC converge\n"
                "- See DIDNOTCONVERGE in the Verilator manual");
        } else {
            __Vchange = _change_request(vlSymsp);
        }
    } while (VL_UNLIKELY(__Vchange));
}

VL_INLINE_OPT void VvGray::_combo__TOP__1(VvGray__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvGray::_combo__TOP__1\n"); );
    VvGray* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    vlTOPp->g = (0xffU & (((IData)(vlTOPp->x) >> 1U) 
                          ^ (IData)(vlTOPp->x)));
    vlTOPp->back = ((0x80U & (IData)(vlTOPp->g)) | 
                    ((0x40U & ((0xffffffc0U & (IData)(vlTOPp->g)) 
                               ^ (0x7fffffc0U & ((IData)(vlTOPp->g) 
                                                 >> 1U)))) 
                     | ((0x20U & ((0xffffffe0U & (IData)(vlTOPp->g)) 
                                  ^ ((0x7fffffe0U & 
                                      ((IData)(vlTOPp->g) 
                                       >> 1U)) ^ (0x3fffffe0U 
                                                  & ((IData)(vlTOPp->g) 
                                                     >> 2U))))) 
                        | ((0x10U & ((0xfffffff0U & (IData)(vlTOPp->g)) 
                                     ^ ((0x7ffffff0U 
                                         & ((IData)(vlTOPp->g) 
                                            >> 1U)) 
                                        ^ ((0x3ffffff0U 
                                            & ((IData)(vlTOPp->g) 
                                               >> 2U)) 
                                           ^ (0x1ffffff0U 
                                              & ((IData)(vlTOPp->g) 
                                                 >> 3U)))))) 
                           | ((8U & ((0xfffffff8U & (IData)(vlTOPp->g)) 
                                     ^ ((0x7ffffff8U 
                                         & ((IData)(vlTOPp->g) 
                                            >> 1U)) 
                                        ^ ((0x3ffffff8U 
                                            & ((IData)(vlTOPp->g) 
                                               >> 2U)) 
                                           ^ ((0x1ffffff8U 
                                               & ((IData)(vlTOPp->g) 
                                                  >> 3U)) 
                                              ^ (0xffffff8U 
                                                 & ((IData)(vlTOPp->g) 
                                                    >> 4U))))))) 
                              | ((4U & ((0xfffffffcU 
                                         & (IData)(vlTOPp->g)) 
                                        ^ ((0x7ffffffcU 
                                            & ((IData)(vlTOPp->g) 
                                               >> 1U)) 
                                           ^ ((0x3ffffffcU 
                                               & ((IData)(vlTOPp->g) 
                                                  >> 2U)) 
                                              ^ ((0x1ffffffcU 
                                                  & ((IData)(vlTOPp->g) 
                                                     >> 3U)) 
                                                 ^ 
                                                 ((0xffffffcU 
                                                   & ((IData)(vlTOPp->g) 
                                                      >> 4U)) 
                                                  ^ 
                                                  (0x7fffffcU 
                                                   & ((IData)(vlTOPp->g) 
                                                      >> 5U)))))))) 
                                 | ((2U & ((0xfffffffeU 
                                            & (IData)(vlTOPp->g)) 
                                           ^ ((0x7ffffffeU 
                                               & ((IData)(vlTOPp->g) 
                                                  >> 1U)) 
                                              ^ ((0x3ffffffeU 
                                                  & ((IData)(vlTOPp->g) 
                                                     >> 2U)) 
                                                 ^ 
                                                 ((0x1ffffffeU 
                                                   & ((IData)(vlTOPp->g) 
                                                      >> 3U)) 
                                                  ^ 
                                                  ((0xffffffeU 
                                                    & ((IData)(vlTOPp->g) 
                                                       >> 4U)) 
                                                   ^ 
                                                   ((0x7fffffeU 
                                                     & ((IData)(vlTOPp->g) 
                                                        >> 5U)) 
                                                    ^ 
                                                    (0x3fffffeU 
                                                     & ((IData)(vlTOPp->g) 
                                                        >> 6U))))))))) 
                                    | (1U & ((IData)(vlTOPp->g) 
                                             ^ (((IData)(vlTOPp->g) 
                                                 >> 1U) 
                                                ^ (
                                                   ((IData)(vlTOPp->g) 
                                                    >> 2U) 
                                                   ^ 
                                                   (((IData)(vlTOPp->g) 
                                                     >> 3U) 
                                                    ^ 
                                                    (((IData)(vlTOPp->g) 
                                                      >> 4U) 
                                                     ^ 
                                                     (((IData)(vlTOPp->g) 
                                                       >> 5U) 
                                                      ^ 
                                                      (((IData)(vlTOPp->g) 
                                                        >> 6U) 
                                                       ^ 
                                                       ((IData)(vlTOPp->g) 
                                                        >> 7U))))))))))))))));
}

void VvGray::_eval(VvGray__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvGray::_eval\n"); );
    VvGray* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    vlTOPp->_combo__TOP__1(vlSymsp);
}

VL_INLINE_OPT QData VvGray::_change_request(VvGray__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvGray::_change_request\n"); );
    VvGray* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    return (vlTOPp->_change_request_1(vlSymsp));
}

VL_INLINE_OPT QData VvGray::_change_request_1(VvGray__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvGray::_change_request_1\n"); );
    VvGray* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    // Change detection
    QData __req = false;  // Logically a bool
    return __req;
}

#ifdef VL_DEBUG
void VvGray::_eval_debug_assertions() {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvGray::_eval_debug_assertions\n"); );
}
#endif  // VL_DEBUG
