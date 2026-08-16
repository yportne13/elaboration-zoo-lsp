
#include "VvClamp.h"
#include "verilated.h"
#include <cstdio>
#include <cstdint>
int main(int argc, char** argv) {
    VvClamp* dut = new VvClamp;
    FILE* f = fopen("/mnt/f/projects/hermes/elaboration-zoo-lsp/tools/spinalhdl-verify/work/vClamp.stim", "r");
    if (!f) return 2;
    uint64_t a; uint64_t lo; uint64_t hi;
    while (fscanf(f, "%llx %llx %llx", &a, &lo, &hi) == 3) {
        dut->a = a;
    dut->lo = lo;
    dut->hi = hi;
        dut->eval();
        printf("%x ", dut->cl);
        printf("\n");
    }
    fclose(f);
    delete dut;
    return 0;
}
