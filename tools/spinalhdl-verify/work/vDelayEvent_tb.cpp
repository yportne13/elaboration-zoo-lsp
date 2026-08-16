
#include "VvDelayEvent.h"
#include "verilated.h"
#include <cstdio>
#include <cstdint>
int main(int argc, char** argv) {
    VvDelayEvent* dut = new VvDelayEvent;
    FILE* f = fopen("/mnt/f/projects/hermes/elaboration-zoo-lsp/tools/spinalhdl-verify/work/vDelayEvent.stim", "r");
    if (!f) return 2;
    uint64_t rst; uint64_t c = 0; int fail = 0;
    uint64_t ev = 0; uint64_t de = 0;
    while (fscanf(f, "%llu %llx %llx", &rst, &ev, &de) == 3) {
                dut->reset = rst;
        dut->ev = ev;
                dut->clk = 0; dut->eval();
        dut->clk = 1; dut->eval();
        if (dut->de != de) { printf("MISMATCH vDelayEvent cycle %llu: got %llx expected %llx\n", c, dut->de, de); fail = 1; }
        c++;
    }
    fclose(f);
    delete dut;
    printf(fail ? "\nFAIL\n" : "\nPASS\n");
    return fail;
}
