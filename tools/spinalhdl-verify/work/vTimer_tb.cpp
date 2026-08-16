
#include "VvTimer.h"
#include "verilated.h"
#include <cstdio>
#include <cstdint>
int main(int argc, char** argv) {
    VvTimer* dut = new VvTimer;
    FILE* f = fopen("/mnt/f/projects/hermes/elaboration-zoo-lsp/tools/spinalhdl-verify/work/vTimer.stim", "r");
    if (!f) return 2;
    uint64_t rst; uint64_t c = 0; int fail = 0;
    uint64_t tick = 0; uint64_t clr = 0; uint64_t lim = 0; uint64_t full = 0; uint64_t value = 0;
    while (fscanf(f, "%llu %llx %llx %llx %llx %llx", &rst, &tick, &clr, &lim, &full, &value) == 6) {
                dut->reset = rst;
        dut->tick = tick;
    dut->clr = clr;
    dut->lim = lim;
                dut->clk = 0; dut->eval();
        dut->clk = 1; dut->eval();
        if (dut->full != full) { printf("MISMATCH vTimer cycle %llu: got %llx expected %llx\n", c, dut->full, full); fail = 1; }
    if (dut->value != value) { printf("MISMATCH vTimer cycle %llu: got %llx expected %llx\n", c, dut->value, value); fail = 1; }
        c++;
    }
    fclose(f);
    delete dut;
    printf(fail ? "\nFAIL\n" : "\nPASS\n");
    return fail;
}
