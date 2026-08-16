
#include "VvDecoder.h"
#include "verilated.h"
#include <cstdio>
#include <cstdint>
int main(int argc, char** argv) {
    VvDecoder* dut = new VvDecoder;
    FILE* f = fopen("/mnt/f/projects/hermes/elaboration-zoo-lsp/tools/spinalhdl-verify/work/vDecoder.stim", "r");
    if (!f) return 2;
    uint64_t oh;
    while (fscanf(f, "%llx", &oh) == 1) {
        dut->oh = oh;
        dut->eval();
        printf("%x ", dut->idx);
        printf("\n");
    }
    fclose(f);
    delete dut;
    return 0;
}
