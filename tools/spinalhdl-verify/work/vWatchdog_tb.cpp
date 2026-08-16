
#include "VvWatchdog.h"
#include "verilated.h"
#include <cstdio>
#include <cstdint>
int main(int argc, char** argv) {
    VvWatchdog* dut = new VvWatchdog;
    FILE* f = fopen("/mnt/f/projects/hermes/elaboration-zoo-lsp/tools/spinalhdl-verify/work/vWatchdog.stim", "r");
    if (!f) return 2;
    uint64_t rst; uint64_t c = 0; int fail = 0;
    uint64_t feed = 0; uint64_t lim = 0; uint64_t timeout = 0;
    while (fscanf(f, "%llu %llx %llx %llx", &rst, &feed, &lim, &timeout) == 4) {
                dut->reset = rst;
        dut->feed = feed;
    dut->lim = lim;
                dut->clk = 0; dut->eval();
        dut->clk = 1; dut->eval();
        if (dut->timeout != timeout) { printf("MISMATCH vWatchdog cycle %llu: got %llx expected %llx\n", c, dut->timeout, timeout); fail = 1; }
        c++;
    }
    fclose(f);
    delete dut;
    printf(fail ? "\nFAIL\n" : "\nPASS\n");
    return fail;
}
