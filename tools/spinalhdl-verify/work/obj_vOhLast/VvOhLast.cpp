// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See VvOhLast.h for the primary calling header

#include "VvOhLast.h"
#include "VvOhLast__Syms.h"

//==========

void VvOhLast::eval_step() {
    VL_DEBUG_IF(VL_DBG_MSGF("+++++TOP Evaluate VvOhLast::eval\n"); );
    VvOhLast__Syms* __restrict vlSymsp = this->__VlSymsp;  // Setup global symbol table
    VvOhLast* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
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
            VL_FATAL_MT("/mnt/f/projects/hermes/elaboration-zoo-lsp/tools/spinalhdl-verify/work/vOhLast.v", 1, "",
                "Verilated model didn't converge\n"
                "- See DIDNOTCONVERGE in the Verilator manual");
        } else {
            __Vchange = _change_request(vlSymsp);
        }
    } while (VL_UNLIKELY(__Vchange));
}

void VvOhLast::_eval_initial_loop(VvOhLast__Syms* __restrict vlSymsp) {
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
            VL_FATAL_MT("/mnt/f/projects/hermes/elaboration-zoo-lsp/tools/spinalhdl-verify/work/vOhLast.v", 1, "",
                "Verilated model didn't DC converge\n"
                "- See DIDNOTCONVERGE in the Verilator manual");
        } else {
            __Vchange = _change_request(vlSymsp);
        }
    } while (VL_UNLIKELY(__Vchange));
}

VL_INLINE_OPT void VvOhLast::_combo__TOP__1(VvOhLast__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvOhLast::_combo__TOP__1\n"); );
    VvOhLast* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    vlTOPp->l = ((IData)(vlTOPp->oh) & ((0x1fU >= (
                                                   (0x80U 
                                                    & (IData)(vlTOPp->oh))
                                                    ? 7U
                                                    : 
                                                   ((0x40U 
                                                     & (IData)(vlTOPp->oh))
                                                     ? 6U
                                                     : 
                                                    ((0x20U 
                                                      & (IData)(vlTOPp->oh))
                                                      ? 5U
                                                      : 
                                                     ((0x10U 
                                                       & (IData)(vlTOPp->oh))
                                                       ? 4U
                                                       : 
                                                      ((8U 
                                                        & (IData)(vlTOPp->oh))
                                                        ? 3U
                                                        : 
                                                       ((4U 
                                                         & (IData)(vlTOPp->oh))
                                                         ? 2U
                                                         : 
                                                        ((2U 
                                                          & (IData)(vlTOPp->oh))
                                                          ? 1U
                                                          : 0U))))))))
                                         ? ((IData)(1U) 
                                            << ((0x80U 
                                                 & (IData)(vlTOPp->oh))
                                                 ? 7U
                                                 : 
                                                ((0x40U 
                                                  & (IData)(vlTOPp->oh))
                                                  ? 6U
                                                  : 
                                                 ((0x20U 
                                                   & (IData)(vlTOPp->oh))
                                                   ? 5U
                                                   : 
                                                  ((0x10U 
                                                    & (IData)(vlTOPp->oh))
                                                    ? 4U
                                                    : 
                                                   ((8U 
                                                     & (IData)(vlTOPp->oh))
                                                     ? 3U
                                                     : 
                                                    ((4U 
                                                      & (IData)(vlTOPp->oh))
                                                      ? 2U
                                                      : 
                                                     ((2U 
                                                       & (IData)(vlTOPp->oh))
                                                       ? 1U
                                                       : 0U))))))))
                                         : 0U));
}

void VvOhLast::_eval(VvOhLast__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvOhLast::_eval\n"); );
    VvOhLast* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    vlTOPp->_combo__TOP__1(vlSymsp);
}

VL_INLINE_OPT QData VvOhLast::_change_request(VvOhLast__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvOhLast::_change_request\n"); );
    VvOhLast* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    return (vlTOPp->_change_request_1(vlSymsp));
}

VL_INLINE_OPT QData VvOhLast::_change_request_1(VvOhLast__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvOhLast::_change_request_1\n"); );
    VvOhLast* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    // Change detection
    QData __req = false;  // Logically a bool
    return __req;
}

#ifdef VL_DEBUG
void VvOhLast::_eval_debug_assertions() {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvOhLast::_eval_debug_assertions\n"); );
}
#endif  // VL_DEBUG
