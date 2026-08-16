
#include "VvScrap.h"
#include "verilated.h"
#include <cstdio>
#include <cstdint>
int main(int argc, char** argv) {
    VvScrap* dut = new VvScrap;
    FILE* f = fopen("/mnt/f/projects/hermes/elaboration-zoo-lsp/tools/spinalhdl-verify/work/vScrap.stim", "r");
    if (!f) return 2;
    uint64_t a; uint64_t sh;
    while (fscanf(f, "%llx %llx", &a, &sh) == 2) {
        dut->a = a;
    dut->sh = sh;
        dut->eval();
        printf("%x ", dut->s);
        printf("\n");
    }
    fclose(f);
    delete dut;
    return 0;
}
