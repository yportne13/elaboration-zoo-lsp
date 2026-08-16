
#include "VvFifoCC.h"
#include "verilated.h"
#include <cstdio>
#include <cstdint>
int main(int argc, char** argv) {
    VvFifoCC* dut = new VvFifoCC;
    FILE* f = fopen("/mnt/f/projects/hermes/elaboration-zoo-lsp/tools/spinalhdl-verify/work/vFifoCC.stim", "r");
    if (!f) return 2;
    uint64_t rst; uint64_t c = 0; int fail = 0;
    uint64_t pushValid = 0; uint64_t pushData = 0; uint64_t pushReady = 0; uint64_t popValid = 0; uint64_t popData = 0;
    while (fscanf(f, "%llu %llx %llx %llx %llx %llx", &rst, &pushValid, &pushData, &pushReady, &popValid, &popData) == 6) {
                dut->rstA = rst;
        dut->rstB = rst;
        dut->pushValid = pushValid;
    dut->pushData = pushData;
                dut->clkA = 0; dut->eval();
        dut->clkB = 0; dut->eval();
        dut->clkA = 1; dut->eval();
        dut->clkB = 1; dut->eval();
        if (dut->pushReady != pushReady) { printf("MISMATCH vFifoCC cycle %llu: got %llx expected %llx\n", c, dut->pushReady, pushReady); fail = 1; }
    if (dut->popValid != popValid) { printf("MISMATCH vFifoCC cycle %llu: got %llx expected %llx\n", c, dut->popValid, popValid); fail = 1; }
    if (dut->popData != popData) { printf("MISMATCH vFifoCC cycle %llu: got %llx expected %llx\n", c, dut->popData, popData); fail = 1; }
        c++;
    }
    fclose(f);
    delete dut;
    printf(fail ? "\nFAIL\n" : "\nPASS\n");
    return fail;
}
