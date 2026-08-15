
#include "VvStreamFork.h"
#include "verilated.h"
#include <cstdio>
#include <cstdint>
int main(int argc, char** argv) {
    VvStreamFork* dut = new VvStreamFork;
    FILE* f = fopen("/mnt/f/projects/hermes/elaboration-zoo-lsp/tools/spinalhdl-verify/work/vStreamFork.stim", "r");
    if (!f) return 2;
    uint64_t rst; uint64_t c = 0; int fail = 0;
    uint64_t in_valid = 0; uint64_t in_payload = 0; uint64_t o0_ready = 0; uint64_t o1_ready = 0; uint64_t in_ready = 0; uint64_t o0_valid = 0; uint64_t o0_payload = 0; uint64_t o1_valid = 0; uint64_t o1_payload = 0;
    while (fscanf(f, "%llu %llx %llx %llx %llx %llx %llx %llx %llx %llx", &rst, &in_valid, &in_payload, &o0_ready, &o1_ready, &in_ready, &o0_valid, &o0_payload, &o1_valid, &o1_payload) == 10) {
        
        dut->in_valid = in_valid;
    dut->in_payload = in_payload;
    dut->o0_ready = o0_ready;
    dut->o1_ready = o1_ready;
                dut->eval();
        if (dut->in_ready != in_ready) { printf("MISMATCH vStreamFork cycle %llu: got %llx expected %llx\n", c, dut->in_ready, in_ready); fail = 1; }
    if (dut->o0_valid != o0_valid) { printf("MISMATCH vStreamFork cycle %llu: got %llx expected %llx\n", c, dut->o0_valid, o0_valid); fail = 1; }
    if (dut->o0_payload != o0_payload) { printf("MISMATCH vStreamFork cycle %llu: got %llx expected %llx\n", c, dut->o0_payload, o0_payload); fail = 1; }
    if (dut->o1_valid != o1_valid) { printf("MISMATCH vStreamFork cycle %llu: got %llx expected %llx\n", c, dut->o1_valid, o1_valid); fail = 1; }
    if (dut->o1_payload != o1_payload) { printf("MISMATCH vStreamFork cycle %llu: got %llx expected %llx\n", c, dut->o1_payload, o1_payload); fail = 1; }
        c++;
    }
    fclose(f);
    delete dut;
    printf(fail ? "\nFAIL\n" : "\nPASS\n");
    return fail;
}
