// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See VvNapot.h for the primary calling header

#include "VvNapot.h"
#include "VvNapot__Syms.h"

//==========

void VvNapot::eval_step() {
    VL_DEBUG_IF(VL_DBG_MSGF("+++++TOP Evaluate VvNapot::eval\n"); );
    VvNapot__Syms* __restrict vlSymsp = this->__VlSymsp;  // Setup global symbol table
    VvNapot* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
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
            VL_FATAL_MT("/mnt/f/projects/hermes/elaboration-zoo-lsp/tools/spinalhdl-verify/work/vNapot.v", 1, "",
                "Verilated model didn't converge\n"
                "- See DIDNOTCONVERGE in the Verilator manual");
        } else {
            __Vchange = _change_request(vlSymsp);
        }
    } while (VL_UNLIKELY(__Vchange));
}

void VvNapot::_eval_initial_loop(VvNapot__Syms* __restrict vlSymsp) {
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
            VL_FATAL_MT("/mnt/f/projects/hermes/elaboration-zoo-lsp/tools/spinalhdl-verify/work/vNapot.v", 1, "",
                "Verilated model didn't DC converge\n"
                "- See DIDNOTCONVERGE in the Verilator manual");
        } else {
            __Vchange = _change_request(vlSymsp);
        }
    } while (VL_UNLIKELY(__Vchange));
}

VL_INLINE_OPT void VvNapot::_combo__TOP__1(VvNapot__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvNapot::_combo__TOP__1\n"); );
    VvNapot* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    vlTOPp->n = (0x1fU & ((0x10U & (((~ (IData)(vlTOPp->a)) 
                                     | ((~ ((IData)(vlTOPp->a) 
                                            >> 1U)) 
                                        | ((~ ((IData)(vlTOPp->a) 
                                               >> 2U)) 
                                           | (~ ((IData)(vlTOPp->a) 
                                                 >> 3U))))) 
                                    << 4U)) | ((8U 
                                                & (((~ (IData)(vlTOPp->a)) 
                                                    | ((~ 
                                                        ((IData)(vlTOPp->a) 
                                                         >> 1U)) 
                                                       | (~ 
                                                          ((IData)(vlTOPp->a) 
                                                           >> 2U)))) 
                                                   << 3U)) 
                                               | ((4U 
                                                   & (((~ (IData)(vlTOPp->a)) 
                                                       | (~ 
                                                          ((IData)(vlTOPp->a) 
                                                           >> 1U))) 
                                                      << 2U)) 
                                                  | (2U 
                                                     & ((~ (IData)(vlTOPp->a)) 
                                                        << 1U))))));
}

void VvNapot::_eval(VvNapot__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvNapot::_eval\n"); );
    VvNapot* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    vlTOPp->_combo__TOP__1(vlSymsp);
}

VL_INLINE_OPT QData VvNapot::_change_request(VvNapot__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvNapot::_change_request\n"); );
    VvNapot* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    return (vlTOPp->_change_request_1(vlSymsp));
}

VL_INLINE_OPT QData VvNapot::_change_request_1(VvNapot__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvNapot::_change_request_1\n"); );
    VvNapot* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    // Change detection
    QData __req = false;  // Logically a bool
    return __req;
}

#ifdef VL_DEBUG
void VvNapot::_eval_debug_assertions() {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvNapot::_eval_debug_assertions\n"); );
    // Body
    if (VL_UNLIKELY((a & 0xf0U))) {
        Verilated::overWidthError("a");}
}
#endif  // VL_DEBUG
