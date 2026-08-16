
#include "VvOhLegal.h"
#include "verilated.h"
#include <cstdio>
#include <cstdint>
int main(int argc, char** argv) {
    VvOhLegal* dut = new VvOhLegal;
    FILE* f = fopen("/mnt/f/projects/hermes/elaboration-zoo-lsp/tools/spinalhdl-verify/work/vOhLegal.stim", "r");
    if (!f) return 2;
    uint64_t oh;
    while (fscanf(f, "%llx", &oh) == 1) {
        dut->oh = oh;
        dut->eval();
        printf("%x ", dut->legal);
        printf("\n");
    }
    fclose(f);
    delete dut;
    return 0;
}
