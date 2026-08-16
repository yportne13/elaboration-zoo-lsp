
#include "VvGray.h"
#include "verilated.h"
#include <cstdio>
#include <cstdint>
int main(int argc, char** argv) {
    VvGray* dut = new VvGray;
    FILE* f = fopen("/mnt/f/projects/hermes/elaboration-zoo-lsp/tools/spinalhdl-verify/work/vGray.stim", "r");
    if (!f) return 2;
    uint64_t x;
    while (fscanf(f, "%llx", &x) == 1) {
        dut->x = x;
        dut->eval();
        printf("%x ", dut->g);printf("%x ", dut->back);
        printf("\n");
    }
    fclose(f);
    delete dut;
    return 0;
}
