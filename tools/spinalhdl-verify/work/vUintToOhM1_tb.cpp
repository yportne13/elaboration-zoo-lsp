
#include "VvUintToOhM1.h"
#include "verilated.h"
#include <cstdio>
#include <cstdint>
int main(int argc, char** argv) {
    VvUintToOhM1* dut = new VvUintToOhM1;
    FILE* f = fopen("/mnt/f/projects/hermes/elaboration-zoo-lsp/tools/spinalhdl-verify/work/vUintToOhM1.stim", "r");
    if (!f) return 2;
    uint64_t a;
    while (fscanf(f, "%llx", &a) == 1) {
        dut->a = a;
        dut->eval();
        printf("%x ", dut->oh);
        printf("\n");
    }
    fclose(f);
    delete dut;
    return 0;
}
