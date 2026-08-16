
#include "VvMuxOH.h"
#include "verilated.h"
#include <cstdio>
#include <cstdint>
int main(int argc, char** argv) {
    VvMuxOH* dut = new VvMuxOH;
    FILE* f = fopen("/mnt/f/projects/hermes/elaboration-zoo-lsp/tools/spinalhdl-verify/work/vMuxOH.stim", "r");
    if (!f) return 2;
    uint64_t sel; uint64_t a; uint64_t b; uint64_t c; uint64_t d;
    while (fscanf(f, "%llx %llx %llx %llx %llx", &sel, &a, &b, &c, &d) == 5) {
        dut->sel = sel;
    dut->a = a;
    dut->b = b;
    dut->c = c;
    dut->d = d;
        dut->eval();
        printf("%x ", dut->o);
        printf("\n");
    }
    fclose(f);
    delete dut;
    return 0;
}
