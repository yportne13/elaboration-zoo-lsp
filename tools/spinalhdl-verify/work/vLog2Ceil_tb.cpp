
#include "VvLog2Ceil.h"
#include "verilated.h"
#include <cstdio>
#include <cstdint>
int main(int argc, char** argv) {
    VvLog2Ceil* dut = new VvLog2Ceil;
    FILE* f = fopen("/mnt/f/projects/hermes/elaboration-zoo-lsp/tools/spinalhdl-verify/work/vLog2Ceil.stim", "r");
    if (!f) return 2;
    uint64_t a;
    while (fscanf(f, "%llx", &a) == 1) {
        dut->a = a;
        dut->eval();
        printf("%x ", dut->lc);
        printf("\n");
    }
    fclose(f);
    delete dut;
    return 0;
}
