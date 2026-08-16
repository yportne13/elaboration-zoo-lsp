
#include "VvCountOneOnEach.h"
#include "verilated.h"
#include <cstdio>
#include <cstdint>
int main(int argc, char** argv) {
    VvCountOneOnEach* dut = new VvCountOneOnEach;
    FILE* f = fopen("/mnt/f/projects/hermes/elaboration-zoo-lsp/tools/spinalhdl-verify/work/vCountOneOnEach.stim", "r");
    if (!f) return 2;
    uint64_t a;
    while (fscanf(f, "%llx", &a) == 1) {
        dut->a = a;
        dut->eval();
        printf("%x ", dut->c1);printf("%x ", dut->c2);printf("%x ", dut->c3);printf("%x ", dut->c4);
        printf("\n");
    }
    fclose(f);
    delete dut;
    return 0;
}
