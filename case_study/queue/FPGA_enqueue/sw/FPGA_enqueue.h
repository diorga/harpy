#ifndef __FPGA_ENQUEUE_H__
#define __FPGA_ENQUEUE_H__ 1

#include "cci_test.h"


class FPGA_enqueue : public CCI_TEST
{
  private:
    enum
    {
        TEST_CSR_BASE = 32
    };

  public:
    FPGA_enqueue(const po::variables_map& vm, SVC_WRAPPER& svc) :
        CCI_TEST(vm, svc),
        totalCycles(0),
        doBufferTests(false)
    {
        memset(testBuffers, 0, sizeof(testBuffers));
    }

    ~FPGA_enqueue() {};

    // Returns 0 on success
    int test();

    uint64_t testNumCyclesExecuted();

  private:
    void reallocTestBuffers();
    // Return true about 20% of the time
    bool rand20();

    void dbgRegDump(uint64_t r);

    uint64_t totalCycles;

    // Used to test VTP malloc/free when --buffer-alloc-test=1
    fpga::types::shared_buffer::ptr_t testBuffers[10];
    bool doBufferTests;
};

#endif // __FPGA_ENQUEUE_H__
