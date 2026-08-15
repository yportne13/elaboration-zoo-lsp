
#include "VvStreamM2s.h"
#include "verilated.h"
#include <cstdio>
#include <cstdint>
int main(int argc, char** argv) {
    VvStreamM2s* dut = new VvStreamM2s;
    FILE* f = fopen("/mnt/f/projects/hermes/elaboration-zoo-lsp/tools/spinalhdl-verify/work/vStreamM2s.stim", "r");
    if (!f) return 2;
    uint64_t rst; uint64_t c = 0; int fail = 0;
    uint64_t push_valid = 0; uint64_t push_payload = 0; uint64_t pop_ready = 0; uint64_t push_ready = 0; uint64_t pop_valid = 0; uint64_t pop_payload = 0;
    while (fscanf(f, "%llu %llx %llx %llx %llx %llx %llx", &rst, &push_valid, &push_payload, &pop_ready, &push_ready, &pop_valid, &pop_payload) == 7) {
                dut->reset = rst;
        dut->push_valid = push_valid;
    dut->push_payload = push_payload;
    dut->pop_ready = pop_ready;
                dut->clk = 0; dut->eval();
        dut->clk = 1; dut->eval();
        if (dut->push_ready != push_ready) { printf("MISMATCH vStreamM2s cycle %llu: got %llx expected %llx\n", c, dut->push_ready, push_ready); fail = 1; }
    if (dut->pop_valid != pop_valid) { printf("MISMATCH vStreamM2s cycle %llu: got %llx expected %llx\n", c, dut->pop_valid, pop_valid); fail = 1; }
    if (dut->pop_payload != pop_payload) { printf("MISMATCH vStreamM2s cycle %llu: got %llx expected %llx\n", c, dut->pop_payload, pop_payload); fail = 1; }
        c++;
    }
    fclose(f);
    delete dut;
    printf(fail ? "\nFAIL\n" : "\nPASS\n");
    return fail;
}
