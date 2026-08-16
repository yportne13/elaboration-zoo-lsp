
#include "VvEndianSwap.h"
#include "verilated.h"
#include <cstdio>
#include <cstdint>
int main(int argc, char** argv) {
    VvEndianSwap* dut = new VvEndianSwap;
    FILE* f = fopen("/mnt/f/projects/hermes/elaboration-zoo-lsp/tools/spinalhdl-verify/work/vEndianSwap.stim", "r");
    if (!f) return 2;
    uint64_t a;
    while (fscanf(f, "%llx", &a) == 1) {
        dut->a = a;
        dut->eval();
        printf("%x ", dut->s);
        printf("\n");
    }
    fclose(f);
    delete dut;
    return 0;
}
