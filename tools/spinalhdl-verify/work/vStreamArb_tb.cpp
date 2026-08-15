
#include "VvStreamArb.h"
#include "verilated.h"
#include <cstdio>
#include <cstdint>
int main(int argc, char** argv) {
    VvStreamArb* dut = new VvStreamArb;
    FILE* f = fopen("/mnt/f/projects/hermes/elaboration-zoo-lsp/tools/spinalhdl-verify/work/vStreamArb.stim", "r");
    if (!f) return 2;
    uint64_t rst; uint64_t c = 0; int fail = 0;
    uint64_t a_valid = 0; uint64_t a_payload = 0; uint64_t b_valid = 0; uint64_t b_payload = 0; uint64_t m_ready = 0; uint64_t a_ready = 0; uint64_t b_ready = 0; uint64_t m_valid = 0; uint64_t m_payload = 0;
    while (fscanf(f, "%llu %llx %llx %llx %llx %llx %llx %llx %llx %llx", &rst, &a_valid, &a_payload, &b_valid, &b_payload, &m_ready, &a_ready, &b_ready, &m_valid, &m_payload) == 10) {
        
        dut->a_valid = a_valid;
    dut->a_payload = a_payload;
    dut->b_valid = b_valid;
    dut->b_payload = b_payload;
    dut->m_ready = m_ready;
                dut->eval();
        if (dut->a_ready != a_ready) { printf("MISMATCH vStreamArb cycle %llu: got %llx expected %llx\n", c, dut->a_ready, a_ready); fail = 1; }
    if (dut->b_ready != b_ready) { printf("MISMATCH vStreamArb cycle %llu: got %llx expected %llx\n", c, dut->b_ready, b_ready); fail = 1; }
    if (dut->m_valid != m_valid) { printf("MISMATCH vStreamArb cycle %llu: got %llx expected %llx\n", c, dut->m_valid, m_valid); fail = 1; }
    if (dut->m_payload != m_payload) { printf("MISMATCH vStreamArb cycle %llu: got %llx expected %llx\n", c, dut->m_payload, m_payload); fail = 1; }
        c++;
    }
    fclose(f);
    delete dut;
    printf(fail ? "\nFAIL\n" : "\nPASS\n");
    return fail;
}
