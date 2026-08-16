
#include "VvMaskedEq.h"
#include "verilated.h"
#include <cstdio>
#include <cstdint>
int main(int argc, char** argv) {
    VvMaskedEq* dut = new VvMaskedEq;
    FILE* f = fopen("/mnt/f/projects/hermes/elaboration-zoo-lsp/tools/spinalhdl-verify/work/vMaskedEq.stim", "r");
    if (!f) return 2;
    uint64_t hard;
    while (fscanf(f, "%llx", &hard) == 1) {
        dut->hard = hard;
        dut->eval();
        printf("%x ", dut->eq);
        printf("\n");
    }
    fclose(f);
    delete dut;
    return 0;
}
