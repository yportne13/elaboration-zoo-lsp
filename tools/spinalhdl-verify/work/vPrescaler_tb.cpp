
#include "VvPrescaler.h"
#include "verilated.h"
#include <cstdio>
#include <cstdint>
int main(int argc, char** argv) {
    VvPrescaler* dut = new VvPrescaler;
    FILE* f = fopen("/mnt/f/projects/hermes/elaboration-zoo-lsp/tools/spinalhdl-verify/work/vPrescaler.stim", "r");
    if (!f) return 2;
    uint64_t rst; uint64_t c = 0; int fail = 0;
    uint64_t lim = 0; uint64_t ov = 0;
    while (fscanf(f, "%llu %llx %llx", &rst, &lim, &ov) == 3) {
                dut->reset = rst;
        dut->lim = lim;
                dut->clk = 0; dut->eval();
        dut->clk = 1; dut->eval();
        if (dut->ov != ov) { printf("MISMATCH vPrescaler cycle %llu: got %llx expected %llx\n", c, dut->ov, ov); fail = 1; }
        c++;
    }
    fclose(f);
    delete dut;
    printf(fail ? "\nFAIL\n" : "\nPASS\n");
    return fail;
}
