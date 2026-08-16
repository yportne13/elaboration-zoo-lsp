
#include "VvMinMax.h"
#include "verilated.h"
#include <cstdio>
#include <cstdint>
int main(int argc, char** argv) {
    VvMinMax* dut = new VvMinMax;
    FILE* f = fopen("/mnt/f/projects/hermes/elaboration-zoo-lsp/tools/spinalhdl-verify/work/vMinMax.stim", "r");
    if (!f) return 2;
    uint64_t a; uint64_t b;
    while (fscanf(f, "%llx %llx", &a, &b) == 2) {
        dut->a = a;
    dut->b = b;
        dut->eval();
        printf("%x ", dut->mn);printf("%x ", dut->mx);
        printf("\n");
    }
    fclose(f);
    delete dut;
    return 0;
}
