// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See VvScrap.h for the primary calling header

#include "VvScrap.h"
#include "VvScrap__Syms.h"

//==========

void VvScrap::eval_step() {
    VL_DEBUG_IF(VL_DBG_MSGF("+++++TOP Evaluate VvScrap::eval\n"); );
    VvScrap__Syms* __restrict vlSymsp = this->__VlSymsp;  // Setup global symbol table
    VvScrap* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
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
            VL_FATAL_MT("/mnt/f/projects/hermes/elaboration-zoo-lsp/tools/spinalhdl-verify/work/vScrap.v", 1, "",
                "Verilated model didn't converge\n"
                "- See DIDNOTCONVERGE in the Verilator manual");
        } else {
            __Vchange = _change_request(vlSymsp);
        }
    } while (VL_UNLIKELY(__Vchange));
}

void VvScrap::_eval_initial_loop(VvScrap__Syms* __restrict vlSymsp) {
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
            VL_FATAL_MT("/mnt/f/projects/hermes/elaboration-zoo-lsp/tools/spinalhdl-verify/work/vScrap.v", 1, "",
                "Verilated model didn't DC converge\n"
                "- See DIDNOTCONVERGE in the Verilator manual");
        } else {
            __Vchange = _change_request(vlSymsp);
        }
    } while (VL_UNLIKELY(__Vchange));
}

VL_INLINE_OPT void VvScrap::_combo__TOP__1(VvScrap__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvScrap::_combo__TOP__1\n"); );
    VvScrap* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    vlTOPp->s = (0xffU & ((((1U & (IData)(vlTOPp->sh))
                             ? ((((2U & (IData)(vlTOPp->sh))
                                   ? ((((4U & (IData)(vlTOPp->sh))
                                         ? ((IData)(vlTOPp->a) 
                                            >> 4U) : (IData)(vlTOPp->a)) 
                                       | (IData)(vlTOPp->a)) 
                                      >> 2U) : (((4U 
                                                  & (IData)(vlTOPp->sh))
                                                  ? 
                                                 ((IData)(vlTOPp->a) 
                                                  >> 4U)
                                                  : (IData)(vlTOPp->a)) 
                                                | (IData)(vlTOPp->a))) 
                                 | (((4U & (IData)(vlTOPp->sh))
                                      ? ((IData)(vlTOPp->a) 
                                         >> 4U) : (IData)(vlTOPp->a)) 
                                    | (IData)(vlTOPp->a))) 
                                >> 1U) : (((2U & (IData)(vlTOPp->sh))
                                            ? ((((4U 
                                                  & (IData)(vlTOPp->sh))
                                                  ? 
                                                 ((IData)(vlTOPp->a) 
                                                  >> 4U)
                                                  : (IData)(vlTOPp->a)) 
                                                | (IData)(vlTOPp->a)) 
                                               >> 2U)
                                            : (((4U 
                                                 & (IData)(vlTOPp->sh))
                                                 ? 
                                                ((IData)(vlTOPp->a) 
                                                 >> 4U)
                                                 : (IData)(vlTOPp->a)) 
                                               | (IData)(vlTOPp->a))) 
                                          | (((4U & (IData)(vlTOPp->sh))
                                               ? ((IData)(vlTOPp->a) 
                                                  >> 4U)
                                               : (IData)(vlTOPp->a)) 
                                             | (IData)(vlTOPp->a)))) 
                           | (((2U & (IData)(vlTOPp->sh))
                                ? ((((4U & (IData)(vlTOPp->sh))
                                      ? ((IData)(vlTOPp->a) 
                                         >> 4U) : (IData)(vlTOPp->a)) 
                                    | (IData)(vlTOPp->a)) 
                                   >> 2U) : (((4U & (IData)(vlTOPp->sh))
                                               ? ((IData)(vlTOPp->a) 
                                                  >> 4U)
                                               : (IData)(vlTOPp->a)) 
                                             | (IData)(vlTOPp->a))) 
                              | (((4U & (IData)(vlTOPp->sh))
                                   ? ((IData)(vlTOPp->a) 
                                      >> 4U) : (IData)(vlTOPp->a)) 
                                 | (IData)(vlTOPp->a)))) 
                          | (((((IData)(vlTOPp->sh) 
                                >> 2U) & (0U != (0xfU 
                                                 & (IData)(vlTOPp->a)))) 
                              | (((IData)(vlTOPp->sh) 
                                  >> 1U) & (0U != (3U 
                                                   & (((4U 
                                                        & (IData)(vlTOPp->sh))
                                                        ? 
                                                       ((IData)(vlTOPp->a) 
                                                        >> 4U)
                                                        : (IData)(vlTOPp->a)) 
                                                      | (IData)(vlTOPp->a)))))) 
                             | ((IData)(vlTOPp->sh) 
                                & (0U != (1U & (((2U 
                                                  & (IData)(vlTOPp->sh))
                                                  ? 
                                                 ((((4U 
                                                     & (IData)(vlTOPp->sh))
                                                     ? 
                                                    ((IData)(vlTOPp->a) 
                                                     >> 4U)
                                                     : (IData)(vlTOPp->a)) 
                                                   | (IData)(vlTOPp->a)) 
                                                  >> 2U)
                                                  : 
                                                 (((4U 
                                                    & (IData)(vlTOPp->sh))
                                                    ? 
                                                   ((IData)(vlTOPp->a) 
                                                    >> 4U)
                                                    : (IData)(vlTOPp->a)) 
                                                  | (IData)(vlTOPp->a))) 
                                                | (((4U 
                                                     & (IData)(vlTOPp->sh))
                                                     ? 
                                                    ((IData)(vlTOPp->a) 
                                                     >> 4U)
                                                     : (IData)(vlTOPp->a)) 
                                                   | (IData)(vlTOPp->a)))))))));
}

void VvScrap::_eval(VvScrap__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvScrap::_eval\n"); );
    VvScrap* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    vlTOPp->_combo__TOP__1(vlSymsp);
}

VL_INLINE_OPT QData VvScrap::_change_request(VvScrap__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvScrap::_change_request\n"); );
    VvScrap* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    return (vlTOPp->_change_request_1(vlSymsp));
}

VL_INLINE_OPT QData VvScrap::_change_request_1(VvScrap__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvScrap::_change_request_1\n"); );
    VvScrap* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    // Change detection
    QData __req = false;  // Logically a bool
    return __req;
}

#ifdef VL_DEBUG
void VvScrap::_eval_debug_assertions() {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvScrap::_eval_debug_assertions\n"); );
    // Body
    if (VL_UNLIKELY((sh & 0xf8U))) {
        Verilated::overWidthError("sh");}
}
#endif  // VL_DEBUG
