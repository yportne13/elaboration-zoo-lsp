
#include "VvInterruptCtrl.h"
#include "verilated.h"
#include <cstdio>
#include <cstdint>
int main(int argc, char** argv) {
    VvInterruptCtrl* dut = new VvInterruptCtrl;
    FILE* f = fopen("/mnt/f/projects/hermes/elaboration-zoo-lsp/tools/spinalhdl-verify/work/vInterruptCtrl.stim", "r");
    if (!f) return 2;
    uint64_t rst; uint64_t c = 0; int fail = 0;
    uint64_t inputs = 0; uint64_t clears = 0; uint64_t masks = 0; uint64_t pend = 0;
    while (fscanf(f, "%llu %llx %llx %llx %llx", &rst, &inputs, &clears, &masks, &pend) == 5) {
                dut->reset = rst;
        dut->inputs = inputs;
    dut->clears = clears;
    dut->masks = masks;
                dut->clk = 0; dut->eval();
        dut->clk = 1; dut->eval();
        if (dut->pend != pend) { printf("MISMATCH vInterruptCtrl cycle %llu: got %llx expected %llx\n", c, dut->pend, pend); fail = 1; }
        c++;
    }
    fclose(f);
    delete dut;
    printf(fail ? "\nFAIL\n" : "\nPASS\n");
    return fail;
}
