
#include "VvBcdAdd.h"
#include "verilated.h"
#include <cstdio>
#include <cstdint>
int main(int argc, char** argv) {
    VvBcdAdd* dut = new VvBcdAdd;
    FILE* f = fopen("/mnt/f/projects/hermes/elaboration-zoo-lsp/tools/spinalhdl-verify/work/vBcdAdd.stim", "r");
    if (!f) return 2;
    uint64_t a; uint64_t b; uint64_t cin;
    while (fscanf(f, "%llx %llx %llx", &a, &b, &cin) == 3) {
        dut->a = a;
    dut->b = b;
    dut->cin = cin;
        dut->eval();
        printf("%x ", dut->s);printf("%x ", dut->co);
        printf("\n");
    }
    fclose(f);
    delete dut;
    return 0;
}
