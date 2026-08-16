
#include "VvCounterUpDown.h"
#include "verilated.h"
#include <cstdio>
#include <cstdint>
int main(int argc, char** argv) {
    VvCounterUpDown* dut = new VvCounterUpDown;
    FILE* f = fopen("/mnt/f/projects/hermes/elaboration-zoo-lsp/tools/spinalhdl-verify/work/vCounterUpDown.stim", "r");
    if (!f) return 2;
    uint64_t rst; uint64_t c = 0; int fail = 0;
    uint64_t inc = 0; uint64_t dec = 0; uint64_t value = 0; uint64_t willOverflowIfInc = 0; uint64_t willUnderflowIfDec = 0; uint64_t willOverflow = 0; uint64_t willUnderflow = 0;
    while (fscanf(f, "%llu %llx %llx %llx %llx %llx %llx %llx", &rst, &inc, &dec, &value, &willOverflowIfInc, &willUnderflowIfDec, &willOverflow, &willUnderflow) == 8) {
                dut->reset = rst;
        dut->inc = inc;
    dut->dec = dec;
                dut->clk = 0; dut->eval();
        dut->clk = 1; dut->eval();
        if (dut->value != value) { printf("MISMATCH vCounterUpDown cycle %llu: got %llx expected %llx\n", c, dut->value, value); fail = 1; }
    if (dut->willOverflowIfInc != willOverflowIfInc) { printf("MISMATCH vCounterUpDown cycle %llu: got %llx expected %llx\n", c, dut->willOverflowIfInc, willOverflowIfInc); fail = 1; }
    if (dut->willUnderflowIfDec != willUnderflowIfDec) { printf("MISMATCH vCounterUpDown cycle %llu: got %llx expected %llx\n", c, dut->willUnderflowIfDec, willUnderflowIfDec); fail = 1; }
    if (dut->willOverflow != willOverflow) { printf("MISMATCH vCounterUpDown cycle %llu: got %llx expected %llx\n", c, dut->willOverflow, willOverflow); fail = 1; }
    if (dut->willUnderflow != willUnderflow) { printf("MISMATCH vCounterUpDown cycle %llu: got %llx expected %llx\n", c, dut->willUnderflow, willUnderflow); fail = 1; }
        c++;
    }
    fclose(f);
    delete dut;
    printf(fail ? "\nFAIL\n" : "\nPASS\n");
    return fail;
}
