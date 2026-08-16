
#include "VvOhLast.h"
#include "verilated.h"
#include <cstdio>
#include <cstdint>
int main(int argc, char** argv) {
    VvOhLast* dut = new VvOhLast;
    FILE* f = fopen("/mnt/f/projects/hermes/elaboration-zoo-lsp/tools/spinalhdl-verify/work/vOhLast.stim", "r");
    if (!f) return 2;
    uint64_t oh;
    while (fscanf(f, "%llx", &oh) == 1) {
        dut->oh = oh;
        dut->eval();
        printf("%x ", dut->l);
        printf("\n");
    }
    fclose(f);
    delete dut;
    return 0;
}
