
#include "VvOhRR.h"
#include "verilated.h"
#include <cstdio>
#include <cstdint>
int main(int argc, char** argv) {
    VvOhRR* dut = new VvOhRR;
    FILE* f = fopen("/mnt/f/projects/hermes/elaboration-zoo-lsp/tools/spinalhdl-verify/work/vOhRR.stim", "r");
    if (!f) return 2;
    uint64_t req; uint64_t pri;
    while (fscanf(f, "%llx %llx", &req, &pri) == 2) {
        dut->req = req;
    dut->pri = pri;
        dut->eval();
        printf("%x ", dut->g);
        printf("\n");
    }
    fclose(f);
    delete dut;
    return 0;
}
