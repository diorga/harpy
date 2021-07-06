#ifndef __<test_name>_H__
#define __<test_name>_H__ 1

#include "cci_test.h"


class <test_name> : public CCI_TEST
{
  private:
    enum
    {
        TEST_CSR_BASE = 32
    };

  public:
    <test_name>(const po::variables_map& vm, SVC_WRAPPER& svc) :
        CCI_TEST(vm, svc),
        totalCycles(0),
        doBufferTests(false)
    {
        memset(testBuffers, 0, sizeof(testBuffers));
    }

    ~<test_name>() {};

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

#endif // _<test_name>_H_
