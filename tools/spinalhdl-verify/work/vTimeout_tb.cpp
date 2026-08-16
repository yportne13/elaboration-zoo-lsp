
#include "VvTimeout.h"
#include "verilated.h"
#include <cstdio>
#include <cstdint>
int main(int argc, char** argv) {
    VvTimeout* dut = new VvTimeout;
    FILE* f = fopen("/mnt/f/projects/hermes/elaboration-zoo-lsp/tools/spinalhdl-verify/work/vTimeout.stim", "r");
    if (!f) return 2;
    uint64_t rst; uint64_t c = 0; int fail = 0;
    uint64_t en = 0; uint64_t ts = 0;
    while (fscanf(f, "%llu %llx %llx", &rst, &en, &ts) == 3) {
                dut->reset = rst;
        dut->en = en;
                dut->clk = 0; dut->eval();
        dut->clk = 1; dut->eval();
        if (dut->ts != ts) { printf("MISMATCH vTimeout cycle %llu: got %llx expected %llx\n", c, dut->ts, ts); fail = 1; }
        c++;
    }
    fclose(f);
    delete dut;
    printf(fail ? "\nFAIL\n" : "\nPASS\n");
    return fail;
}
