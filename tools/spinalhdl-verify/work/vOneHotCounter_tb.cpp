
#include "VvOneHotCounter.h"
#include "verilated.h"
#include <cstdio>
#include <cstdint>
int main(int argc, char** argv) {
    VvOneHotCounter* dut = new VvOneHotCounter;
    FILE* f = fopen("/mnt/f/projects/hermes/elaboration-zoo-lsp/tools/spinalhdl-verify/work/vOneHotCounter.stim", "r");
    if (!f) return 2;
    uint64_t rst; uint64_t c = 0; int fail = 0;
    uint64_t en = 0;
    while (fscanf(f, "%llu %llx %llx %llx", &rst, &en, &value, &willOverflow) == 4) {
        dut->reset = rst;
        dut->en = en;
        dut->clk = 0; dut->eval();
        dut->clk = 1; dut->eval();
        if (dut->value != value) { printf("MISMATCH vOneHotCounter cycle %llu: got %llx expected %llx\n", c, dut->value, value); fail = 1; }
    if (dut->willOverflow != willOverflow) { printf("MISMATCH vOneHotCounter cycle %llu: got %llx expected %llx\n", c, dut->willOverflow, willOverflow); fail = 1; }
        c++;
    }
    fclose(f);
    delete dut;
    printf(fail ? "\nFAIL\n" : "\nPASS\n");
    return fail;
}
