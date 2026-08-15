// Verilated -*- C++ -*-
// DESCRIPTION: Verilator output: Design implementation internals
// See VvCounterUpDown.h for the primary calling header

#include "VvCounterUpDown.h"
#include "VvCounterUpDown__Syms.h"

//==========
CData/*3:0*/ VvCounterUpDown::__Vtable1_vCounterUpDown__DOT__ud[128];

VL_CTOR_IMP(VvCounterUpDown) {
    VvCounterUpDown__Syms* __restrict vlSymsp = __VlSymsp = new VvCounterUpDown__Syms(this, name());
    VvCounterUpDown* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Reset internal values
    
    // Reset structure values
    _ctor_var_reset();
}

void VvCounterUpDown::__Vconfigure(VvCounterUpDown__Syms* vlSymsp, bool first) {
    if (false && first) {}  // Prevent unused
    this->__VlSymsp = vlSymsp;
    if (false && this->__VlSymsp) {}  // Prevent unused
    Verilated::timeunit(-12);
    Verilated::timeprecision(-12);
}

VvCounterUpDown::~VvCounterUpDown() {
    VL_DO_CLEAR(delete __VlSymsp, __VlSymsp = NULL);
}

void VvCounterUpDown::_settle__TOP__2(VvCounterUpDown__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvCounterUpDown::_settle__TOP__2\n"); );
    VvCounterUpDown* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    vlTOPp->value = vlTOPp->vCounterUpDown__DOT__ud;
    vlTOPp->willOverflowIfInc = (9U == (IData)(vlTOPp->vCounterUpDown__DOT__ud));
    vlTOPp->willUnderflowIfDec = (0U == (IData)(vlTOPp->vCounterUpDown__DOT__ud));
    vlTOPp->willOverflow = (((IData)(vlTOPp->inc) & 
                             (~ (IData)(vlTOPp->dec))) 
                            & (9U == (IData)(vlTOPp->vCounterUpDown__DOT__ud)));
    vlTOPp->willUnderflow = (((IData)(vlTOPp->dec) 
                              & (~ (IData)(vlTOPp->inc))) 
                             & (0U == (IData)(vlTOPp->vCounterUpDown__DOT__ud)));
}

void VvCounterUpDown::_eval_initial(VvCounterUpDown__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvCounterUpDown::_eval_initial\n"); );
    VvCounterUpDown* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    vlTOPp->__Vclklast__TOP__clk = vlTOPp->clk;
    vlTOPp->__Vclklast__TOP__reset = vlTOPp->reset;
}

void VvCounterUpDown::final() {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvCounterUpDown::final\n"); );
    // Variables
    VvCounterUpDown__Syms* __restrict vlSymsp = this->__VlSymsp;
    VvCounterUpDown* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
}

void VvCounterUpDown::_eval_settle(VvCounterUpDown__Syms* __restrict vlSymsp) {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvCounterUpDown::_eval_settle\n"); );
    VvCounterUpDown* const __restrict vlTOPp VL_ATTR_UNUSED = vlSymsp->TOPp;
    // Body
    vlTOPp->_settle__TOP__2(vlSymsp);
}

void VvCounterUpDown::_ctor_var_reset() {
    VL_DEBUG_IF(VL_DBG_MSGF("+    VvCounterUpDown::_ctor_var_reset\n"); );
    // Body
    inc = VL_RAND_RESET_I(1);
    dec = VL_RAND_RESET_I(1);
    value = VL_RAND_RESET_I(4);
    willOverflowIfInc = VL_RAND_RESET_I(1);
    willUnderflowIfDec = VL_RAND_RESET_I(1);
    willOverflow = VL_RAND_RESET_I(1);
    willUnderflow = VL_RAND_RESET_I(1);
    clk = VL_RAND_RESET_I(1);
    reset = VL_RAND_RESET_I(1);
    vCounterUpDown__DOT__ud = VL_RAND_RESET_I(4);
    __Vtablechg1[0] = 0U;
    __Vtablechg1[1] = 1U;
    __Vtablechg1[2] = 1U;
    __Vtablechg1[3] = 1U;
    __Vtablechg1[4] = 1U;
    __Vtablechg1[5] = 1U;
    __Vtablechg1[6] = 0U;
    __Vtablechg1[7] = 1U;
    __Vtablechg1[8] = 0U;
    __Vtablechg1[9] = 1U;
    __Vtablechg1[10] = 1U;
    __Vtablechg1[11] = 1U;
    __Vtablechg1[12] = 1U;
    __Vtablechg1[13] = 1U;
    __Vtablechg1[14] = 0U;
    __Vtablechg1[15] = 1U;
    __Vtablechg1[16] = 0U;
    __Vtablechg1[17] = 1U;
    __Vtablechg1[18] = 1U;
    __Vtablechg1[19] = 1U;
    __Vtablechg1[20] = 1U;
    __Vtablechg1[21] = 1U;
    __Vtablechg1[22] = 0U;
    __Vtablechg1[23] = 1U;
    __Vtablechg1[24] = 0U;
    __Vtablechg1[25] = 1U;
    __Vtablechg1[26] = 1U;
    __Vtablechg1[27] = 1U;
    __Vtablechg1[28] = 1U;
    __Vtablechg1[29] = 1U;
    __Vtablechg1[30] = 0U;
    __Vtablechg1[31] = 1U;
    __Vtablechg1[32] = 0U;
    __Vtablechg1[33] = 1U;
    __Vtablechg1[34] = 1U;
    __Vtablechg1[35] = 1U;
    __Vtablechg1[36] = 1U;
    __Vtablechg1[37] = 1U;
    __Vtablechg1[38] = 0U;
    __Vtablechg1[39] = 1U;
    __Vtablechg1[40] = 0U;
    __Vtablechg1[41] = 1U;
    __Vtablechg1[42] = 1U;
    __Vtablechg1[43] = 1U;
    __Vtablechg1[44] = 1U;
    __Vtablechg1[45] = 1U;
    __Vtablechg1[46] = 0U;
    __Vtablechg1[47] = 1U;
    __Vtablechg1[48] = 0U;
    __Vtablechg1[49] = 1U;
    __Vtablechg1[50] = 1U;
    __Vtablechg1[51] = 1U;
    __Vtablechg1[52] = 1U;
    __Vtablechg1[53] = 1U;
    __Vtablechg1[54] = 0U;
    __Vtablechg1[55] = 1U;
    __Vtablechg1[56] = 0U;
    __Vtablechg1[57] = 1U;
    __Vtablechg1[58] = 1U;
    __Vtablechg1[59] = 1U;
    __Vtablechg1[60] = 1U;
    __Vtablechg1[61] = 1U;
    __Vtablechg1[62] = 0U;
    __Vtablechg1[63] = 1U;
    __Vtablechg1[64] = 0U;
    __Vtablechg1[65] = 1U;
    __Vtablechg1[66] = 1U;
    __Vtablechg1[67] = 1U;
    __Vtablechg1[68] = 1U;
    __Vtablechg1[69] = 1U;
    __Vtablechg1[70] = 0U;
    __Vtablechg1[71] = 1U;
    __Vtablechg1[72] = 0U;
    __Vtablechg1[73] = 1U;
    __Vtablechg1[74] = 1U;
    __Vtablechg1[75] = 1U;
    __Vtablechg1[76] = 1U;
    __Vtablechg1[77] = 1U;
    __Vtablechg1[78] = 0U;
    __Vtablechg1[79] = 1U;
    __Vtablechg1[80] = 0U;
    __Vtablechg1[81] = 1U;
    __Vtablechg1[82] = 1U;
    __Vtablechg1[83] = 1U;
    __Vtablechg1[84] = 1U;
    __Vtablechg1[85] = 1U;
    __Vtablechg1[86] = 0U;
    __Vtablechg1[87] = 1U;
    __Vtablechg1[88] = 0U;
    __Vtablechg1[89] = 1U;
    __Vtablechg1[90] = 1U;
    __Vtablechg1[91] = 1U;
    __Vtablechg1[92] = 1U;
    __Vtablechg1[93] = 1U;
    __Vtablechg1[94] = 0U;
    __Vtablechg1[95] = 1U;
    __Vtablechg1[96] = 0U;
    __Vtablechg1[97] = 1U;
    __Vtablechg1[98] = 1U;
    __Vtablechg1[99] = 1U;
    __Vtablechg1[100] = 1U;
    __Vtablechg1[101] = 1U;
    __Vtablechg1[102] = 0U;
    __Vtablechg1[103] = 1U;
    __Vtablechg1[104] = 0U;
    __Vtablechg1[105] = 1U;
    __Vtablechg1[106] = 1U;
    __Vtablechg1[107] = 1U;
    __Vtablechg1[108] = 1U;
    __Vtablechg1[109] = 1U;
    __Vtablechg1[110] = 0U;
    __Vtablechg1[111] = 1U;
    __Vtablechg1[112] = 0U;
    __Vtablechg1[113] = 1U;
    __Vtablechg1[114] = 1U;
    __Vtablechg1[115] = 1U;
    __Vtablechg1[116] = 1U;
    __Vtablechg1[117] = 1U;
    __Vtablechg1[118] = 0U;
    __Vtablechg1[119] = 1U;
    __Vtablechg1[120] = 0U;
    __Vtablechg1[121] = 1U;
    __Vtablechg1[122] = 1U;
    __Vtablechg1[123] = 1U;
    __Vtablechg1[124] = 1U;
    __Vtablechg1[125] = 1U;
    __Vtablechg1[126] = 0U;
    __Vtablechg1[127] = 1U;
    __Vtable1_vCounterUpDown__DOT__ud[0] = 0U;
    __Vtable1_vCounterUpDown__DOT__ud[1] = 0U;
    __Vtable1_vCounterUpDown__DOT__ud[2] = 1U;
    __Vtable1_vCounterUpDown__DOT__ud[3] = 0U;
    __Vtable1_vCounterUpDown__DOT__ud[4] = 9U;
    __Vtable1_vCounterUpDown__DOT__ud[5] = 0U;
    __Vtable1_vCounterUpDown__DOT__ud[6] = 0U;
    __Vtable1_vCounterUpDown__DOT__ud[7] = 0U;
    __Vtable1_vCounterUpDown__DOT__ud[8] = 0U;
    __Vtable1_vCounterUpDown__DOT__ud[9] = 0U;
    __Vtable1_vCounterUpDown__DOT__ud[10] = 2U;
    __Vtable1_vCounterUpDown__DOT__ud[11] = 0U;
    __Vtable1_vCounterUpDown__DOT__ud[12] = 0U;
    __Vtable1_vCounterUpDown__DOT__ud[13] = 0U;
    __Vtable1_vCounterUpDown__DOT__ud[14] = 0U;
    __Vtable1_vCounterUpDown__DOT__ud[15] = 0U;
    __Vtable1_vCounterUpDown__DOT__ud[16] = 0U;
    __Vtable1_vCounterUpDown__DOT__ud[17] = 0U;
    __Vtable1_vCounterUpDown__DOT__ud[18] = 3U;
    __Vtable1_vCounterUpDown__DOT__ud[19] = 0U;
    __Vtable1_vCounterUpDown__DOT__ud[20] = 1U;
    __Vtable1_vCounterUpDown__DOT__ud[21] = 0U;
    __Vtable1_vCounterUpDown__DOT__ud[22] = 0U;
    __Vtable1_vCounterUpDown__DOT__ud[23] = 0U;
    __Vtable1_vCounterUpDown__DOT__ud[24] = 0U;
    __Vtable1_vCounterUpDown__DOT__ud[25] = 0U;
    __Vtable1_vCounterUpDown__DOT__ud[26] = 4U;
    __Vtable1_vCounterUpDown__DOT__ud[27] = 0U;
    __Vtable1_vCounterUpDown__DOT__ud[28] = 2U;
    __Vtable1_vCounterUpDown__DOT__ud[29] = 0U;
    __Vtable1_vCounterUpDown__DOT__ud[30] = 0U;
    __Vtable1_vCounterUpDown__DOT__ud[31] = 0U;
    __Vtable1_vCounterUpDown__DOT__ud[32] = 0U;
    __Vtable1_vCounterUpDown__DOT__ud[33] = 0U;
    __Vtable1_vCounterUpDown__DOT__ud[34] = 5U;
    __Vtable1_vCounterUpDown__DOT__ud[35] = 0U;
    __Vtable1_vCounterUpDown__DOT__ud[36] = 3U;
    __Vtable1_vCounterUpDown__DOT__ud[37] = 0U;
    __Vtable1_vCounterUpDown__DOT__ud[38] = 0U;
    __Vtable1_vCounterUpDown__DOT__ud[39] = 0U;
    __Vtable1_vCounterUpDown__DOT__ud[40] = 0U;
    __Vtable1_vCounterUpDown__DOT__ud[41] = 0U;
    __Vtable1_vCounterUpDown__DOT__ud[42] = 6U;
    __Vtable1_vCounterUpDown__DOT__ud[43] = 0U;
    __Vtable1_vCounterUpDown__DOT__ud[44] = 4U;
    __Vtable1_vCounterUpDown__DOT__ud[45] = 0U;
    __Vtable1_vCounterUpDown__DOT__ud[46] = 0U;
    __Vtable1_vCounterUpDown__DOT__ud[47] = 0U;
    __Vtable1_vCounterUpDown__DOT__ud[48] = 0U;
    __Vtable1_vCounterUpDown__DOT__ud[49] = 0U;
    __Vtable1_vCounterUpDown__DOT__ud[50] = 7U;
    __Vtable1_vCounterUpDown__DOT__ud[51] = 0U;
    __Vtable1_vCounterUpDown__DOT__ud[52] = 5U;
    __Vtable1_vCounterUpDown__DOT__ud[53] = 0U;
    __Vtable1_vCounterUpDown__DOT__ud[54] = 0U;
    __Vtable1_vCounterUpDown__DOT__ud[55] = 0U;
    __Vtable1_vCounterUpDown__DOT__ud[56] = 0U;
    __Vtable1_vCounterUpDown__DOT__ud[57] = 0U;
    __Vtable1_vCounterUpDown__DOT__ud[58] = 8U;
    __Vtable1_vCounterUpDown__DOT__ud[59] = 0U;
    __Vtable1_vCounterUpDown__DOT__ud[60] = 6U;
    __Vtable1_vCounterUpDown__DOT__ud[61] = 0U;
    __Vtable1_vCounterUpDown__DOT__ud[62] = 0U;
    __Vtable1_vCounterUpDown__DOT__ud[63] = 0U;
    __Vtable1_vCounterUpDown__DOT__ud[64] = 0U;
    __Vtable1_vCounterUpDown__DOT__ud[65] = 0U;
    __Vtable1_vCounterUpDown__DOT__ud[66] = 9U;
    __Vtable1_vCounterUpDown__DOT__ud[67] = 0U;
    __Vtable1_vCounterUpDown__DOT__ud[68] = 7U;
    __Vtable1_vCounterUpDown__DOT__ud[69] = 0U;
    __Vtable1_vCounterUpDown__DOT__ud[70] = 0U;
    __Vtable1_vCounterUpDown__DOT__ud[71] = 0U;
    __Vtable1_vCounterUpDown__DOT__ud[72] = 0U;
    __Vtable1_vCounterUpDown__DOT__ud[73] = 0U;
    __Vtable1_vCounterUpDown__DOT__ud[74] = 0U;
    __Vtable1_vCounterUpDown__DOT__ud[75] = 0U;
    __Vtable1_vCounterUpDown__DOT__ud[76] = 8U;
    __Vtable1_vCounterUpDown__DOT__ud[77] = 0U;
    __Vtable1_vCounterUpDown__DOT__ud[78] = 0U;
    __Vtable1_vCounterUpDown__DOT__ud[79] = 0U;
    __Vtable1_vCounterUpDown__DOT__ud[80] = 0U;
    __Vtable1_vCounterUpDown__DOT__ud[81] = 0U;
    __Vtable1_vCounterUpDown__DOT__ud[82] = 0xbU;
    __Vtable1_vCounterUpDown__DOT__ud[83] = 0U;
    __Vtable1_vCounterUpDown__DOT__ud[84] = 9U;
    __Vtable1_vCounterUpDown__DOT__ud[85] = 0U;
    __Vtable1_vCounterUpDown__DOT__ud[86] = 0U;
    __Vtable1_vCounterUpDown__DOT__ud[87] = 0U;
    __Vtable1_vCounterUpDown__DOT__ud[88] = 0U;
    __Vtable1_vCounterUpDown__DOT__ud[89] = 0U;
    __Vtable1_vCounterUpDown__DOT__ud[90] = 0xcU;
    __Vtable1_vCounterUpDown__DOT__ud[91] = 0U;
    __Vtable1_vCounterUpDown__DOT__ud[92] = 0xaU;
    __Vtable1_vCounterUpDown__DOT__ud[93] = 0U;
    __Vtable1_vCounterUpDown__DOT__ud[94] = 0U;
    __Vtable1_vCounterUpDown__DOT__ud[95] = 0U;
    __Vtable1_vCounterUpDown__DOT__ud[96] = 0U;
    __Vtable1_vCounterUpDown__DOT__ud[97] = 0U;
    __Vtable1_vCounterUpDown__DOT__ud[98] = 0xdU;
    __Vtable1_vCounterUpDown__DOT__ud[99] = 0U;
    __Vtable1_vCounterUpDown__DOT__ud[100] = 0xbU;
    __Vtable1_vCounterUpDown__DOT__ud[101] = 0U;
    __Vtable1_vCounterUpDown__DOT__ud[102] = 0U;
    __Vtable1_vCounterUpDown__DOT__ud[103] = 0U;
    __Vtable1_vCounterUpDown__DOT__ud[104] = 0U;
    __Vtable1_vCounterUpDown__DOT__ud[105] = 0U;
    __Vtable1_vCounterUpDown__DOT__ud[106] = 0xeU;
    __Vtable1_vCounterUpDown__DOT__ud[107] = 0U;
    __Vtable1_vCounterUpDown__DOT__ud[108] = 0xcU;
    __Vtable1_vCounterUpDown__DOT__ud[109] = 0U;
    __Vtable1_vCounterUpDown__DOT__ud[110] = 0U;
    __Vtable1_vCounterUpDown__DOT__ud[111] = 0U;
    __Vtable1_vCounterUpDown__DOT__ud[112] = 0U;
    __Vtable1_vCounterUpDown__DOT__ud[113] = 0U;
    __Vtable1_vCounterUpDown__DOT__ud[114] = 0xfU;
    __Vtable1_vCounterUpDown__DOT__ud[115] = 0U;
    __Vtable1_vCounterUpDown__DOT__ud[116] = 0xdU;
    __Vtable1_vCounterUpDown__DOT__ud[117] = 0U;
    __Vtable1_vCounterUpDown__DOT__ud[118] = 0U;
    __Vtable1_vCounterUpDown__DOT__ud[119] = 0U;
    __Vtable1_vCounterUpDown__DOT__ud[120] = 0U;
    __Vtable1_vCounterUpDown__DOT__ud[121] = 0U;
    __Vtable1_vCounterUpDown__DOT__ud[122] = 0U;
    __Vtable1_vCounterUpDown__DOT__ud[123] = 0U;
    __Vtable1_vCounterUpDown__DOT__ud[124] = 0xeU;
    __Vtable1_vCounterUpDown__DOT__ud[125] = 0U;
    __Vtable1_vCounterUpDown__DOT__ud[126] = 0U;
    __Vtable1_vCounterUpDown__DOT__ud[127] = 0U;
}
