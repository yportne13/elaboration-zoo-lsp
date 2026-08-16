
#include "VvReverse.h"
#include "verilated.h"
#include <cstdio>
#include <cstdint>
int main(int argc, char** argv) {
    VvReverse* dut = new VvReverse;
    FILE* f = fopen("/mnt/f/projects/hermes/elaboration-zoo-lsp/tools/spinalhdl-verify/work/vReverse.stim", "r");
    if (!f) return 2;
    uint64_t a;
    while (fscanf(f, "%llx", &a) == 1) {
        dut->a = a;
        dut->eval();
        printf("%x ", dut->r);
        printf("\n");
    }
    fclose(f);
    delete dut;
    return 0;
}
