
#include "VvAddCarry.h"
#include "verilated.h"
#include <cstdio>
#include <cstdint>
int main(int argc, char** argv) {
    VvAddCarry* dut = new VvAddCarry;
    FILE* f = fopen("/mnt/f/projects/hermes/elaboration-zoo-lsp/tools/spinalhdl-verify/work/vAddCarry.stim", "r");
    if (!f) return 2;
    uint64_t a; uint64_t b;
    while (fscanf(f, "%llx %llx", &a, &b) == 2) {
        dut->a = a;
    dut->b = b;
        dut->eval();
        printf("%x ", dut->sum);printf("%x ", dut->carry);
        printf("\n");
    }
    fclose(f);
    delete dut;
    return 0;
}
