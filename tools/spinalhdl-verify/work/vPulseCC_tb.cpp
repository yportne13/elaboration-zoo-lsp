
#include "VvPulseCC.h"
#include "verilated.h"
#include <cstdio>
#include <cstdint>
int main(int argc, char** argv) {
    VvPulseCC* dut = new VvPulseCC;
    FILE* f = fopen("/mnt/f/projects/hermes/elaboration-zoo-lsp/tools/spinalhdl-verify/work/vPulseCC.stim", "r");
    if (!f) return 2;
    uint64_t rst; uint64_t c = 0; int fail = 0;
    uint64_t pulseIn = 0; uint64_t pulseOut = 0;
    while (fscanf(f, "%llu %llx %llx", &rst, &pulseIn, &pulseOut) == 3) {
        
        dut->pulseIn = pulseIn;
                dut->clkA = 0; dut->eval();
        dut->clkB = 0; dut->eval();
        dut->clkA = 1; dut->eval();
        dut->clkB = 1; dut->eval();
        if (dut->pulseOut != pulseOut) { printf("MISMATCH vPulseCC cycle %llu: got %llx expected %llx\n", c, dut->pulseOut, pulseOut); fail = 1; }
        c++;
    }
    fclose(f);
    delete dut;
    printf(fail ? "\nFAIL\n" : "\nPASS\n");
    return fail;
}
