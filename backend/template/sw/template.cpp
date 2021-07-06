#include "<test_name>.h"
// Generated from the AFU JSON file by afu_json_mgr
#include "afu_json_info.h"

#include <unistd.h>
#include <time.h>
#include <boost/format.hpp>
#include <boost/algorithm/string.hpp>
#include <stdlib.h>
#include <sys/mman.h>
#include <chrono>
#include <thread>

#include "common.h"

#define ELEM_LINE   8


// ========================================================================
//
// Each test must provide these functions used by main to find the
// specific test instance.
//
// ========================================================================

const char* testAFUID()
{
    return AFU_ACCEL_UUID;
}

void testConfigOptions(po::options_description &desc)
{
    // Add test-specific options
    desc.add_options()
      ("repeat,r", po::value<int>()->default_value(10), "Number of repetitions")
      ("VL0_enemy", po::value<int>()->default_value(0), "Activate a VL0 enemy, a higher number coresponds to a higher frequency")
      ("VH0_enemy", po::value<int>()->default_value(0), "Activate a VH0 enemy, a higher number coresponds to a higher frequency")
      ("VH1_enemy", po::value<int>()->default_value(0), "Activate a VH0 enemy, a higher number coresponds to a higher frequency")
      ;

}

CCI_TEST* allocTest(const po::variables_map& vm, SVC_WRAPPER& svc)
{
    return new <test_name>(vm, svc);
}

#define WR_REQ          1
#define WR_RSP          2
#define RD_REQ          3
#define RD_RSP          4
#define FN_REQ          5
#define FN_RSP          6
#define FN_REQANY       5
#define FN_RSPANY       6

#define X_ADDR          0
#define Y_ADDR          1
#define Z_ADDR          2

#define VA              0
#define VL0 	          1
#define VH0 	          2
#define VH1 	          3

uint64_t *r0, *r1, *r2;

<thread_declaration>

// ========================================================================
//
// <test_name>
//
// ========================================================================

int <test_name>::test()
{

    uint64_t repeat = 10000;
    uint64_t experiments_repeat = uint64_t(vm["repeat"].as<int>());

    uint64_t VL0_enemy = uint64_t(vm["VL0_enemy"].as<int>());
    uint64_t VH0_enemy = uint64_t(vm["VH0_enemy"].as<int>());
    uint64_t VH1_enemy = uint64_t(vm["VH1_enemy"].as<int>());

    // Allocate the registers for reads
    r0 = (uint64_t*) calloc(repeat, sizeof(uint64_t) );
    r1 = (uint64_t*) calloc(repeat, sizeof(uint64_t) );
    r2 = (uint64_t*) calloc(repeat, sizeof(uint64_t) );

    // Allocate memory for the x array
    auto x_buf_handle = this->allocBuffer( repeat * ELEM_LINE * sizeof(uint64_t) );
    auto x_buf = reinterpret_cast<volatile uint64_t*>(x_buf_handle->c_type());
    assert(NULL != x_buf);
    setArray(const_cast<uint64_t*>(x_buf), 42, repeat * ELEM_LINE);
    // Initialize the x array in the buffer

    // Allocate memory for the y array
    auto y_buf_handle = this->allocBuffer( repeat * ELEM_LINE * sizeof(uint64_t) );
    auto y_buf = reinterpret_cast<volatile uint64_t*>(y_buf_handle->c_type());
    assert(NULL != y_buf);
    // Initialize the y array in the buffer
    setArray(const_cast<uint64_t*>(y_buf), 42, repeat * ELEM_LINE);

    // Allocate memory for the z array
    auto z_buf_handle = this->allocBuffer( repeat * ELEM_LINE * sizeof(uint64_t) );
    auto z_buf = reinterpret_cast<volatile uint64_t*>(z_buf_handle->c_type());
    assert(NULL != z_buf);
    // Initialize the z array in the buffer
    setArray(const_cast<uint64_t*>(z_buf), 42,  repeat * ELEM_LINE);

    // Allocate memory for the read_registers array
    auto read_registers_buf_handle = this->allocBuffer( repeat * ELEM_LINE * sizeof(uint64_t) );
    auto read_registers_buf = reinterpret_cast<volatile uint64_t*>(read_registers_buf_handle->c_type());
    assert(NULL != read_registers_buf);
    // Initialize the read register in the buffer
    setArray(const_cast<uint64_t*>(read_registers_buf), 42,  repeat * ELEM_LINE);

    // Allocate memory for the ok array
    auto valid_buf_handle = this->allocBuffer( repeat * ELEM_LINE * sizeof(uint64_t) );
    auto valid_buf = reinterpret_cast<volatile uint64_t*>(valid_buf_handle->c_type());
    assert(NULL != valid_buf);
    // Initialize the ok array in the buffer
    setArray(const_cast<uint64_t*>(valid_buf), 42,  repeat * ELEM_LINE);

    // Allocate memory for array that singals finish array
    auto finish_buf_handle = this->allocBuffer( 4* ELEM_LINE * sizeof(uint64_t) );
    auto finish_buf = reinterpret_cast<volatile uint64_t*>(finish_buf_handle->c_type());
    assert(NULL != finish_buf);
    // Initialize the finish array in the buffer
    setArray(const_cast<uint64_t*>(finish_buf), 42, 4*ELEM_LINE);

    //
    // Configure the HW test
    //
    writeTestCSR(1, intptr_t(x_buf));
    writeTestCSR(2, intptr_t(y_buf));
    writeTestCSR(3, intptr_t(z_buf));
    writeTestCSR(4, intptr_t(read_registers_buf));
    writeTestCSR(5, intptr_t(valid_buf));
    writeTestCSR(6, intptr_t(finish_buf));


    uint64_t vl0_lines = readCommonCSR(CCI_TEST::CSR_COMMON_VL0_RD_LINES) +
                         readCommonCSR(CCI_TEST::CSR_COMMON_VL0_WR_LINES);
    uint64_t vh0_lines = readCommonCSR(CCI_TEST::CSR_COMMON_VH0_LINES);
    uint64_t vh1_lines = readCommonCSR(CCI_TEST::CSR_COMMON_VH1_LINES);

    uint64_t va_req_lines = readCommonCSR(CCI_TEST::CSR_COMMON_VA_REQ_LINES);
    uint64_t vl0_req_lines = readCommonCSR(CCI_TEST::CSR_COMMON_VL0_REQ_LINES);
    uint64_t vh0_req_lines = readCommonCSR(CCI_TEST::CSR_COMMON_VH0_REQ_LINES);
    uint64_t vh1_req_lines = readCommonCSR(CCI_TEST::CSR_COMMON_VH1_REQ_LINES);

    writeTestCSR(7, VL0_enemy);
    writeTestCSR(8, VH0_enemy);
    writeTestCSR(9, VH1_enemy);

    writeTestCSR(10, repeat);

<fpga_thread>

    cout << "x buff address " << hex << intptr_t(x_buf) << endl;
    cout << "y buff address " << hex << intptr_t(y_buf) << endl;
    cout << "z buff address " << hex << intptr_t(z_buf) << endl << endl;
    cout << "read_registers buff address " << hex << intptr_t(read_registers_buf) << endl << endl;
    cout << "valid buff address " << hex << intptr_t(valid_buf) << endl << endl;
    cout << "finish buff address " << hex << intptr_t(finish_buf) << endl << endl;

    cout << "Repeating " << dec << repeat << " times" << endl;
    cout << endl << "Spin, waiting for the value in memory to change to something non-42" << endl;

    std::chrono::high_resolution_clock::time_point time1 = std::chrono::high_resolution_clock::now();
    struct timespec pause;
    // Longer when simulating
    pause.tv_sec = (hwIsSimulated() ? 3 : 0);
    pause.tv_nsec = 2500000;

    int valid_traces = 0;
    int valid_test = 1;
    for(int exp = 0; exp<experiments_repeat; exp++) {
        setArray(const_cast<uint64_t*>(x_buf), 42, repeat * ELEM_LINE);
        setArray(const_cast<uint64_t*>(y_buf), 42, repeat * ELEM_LINE);
        setArray(const_cast<uint64_t*>(z_buf), 42,  repeat * ELEM_LINE);
        setArray(const_cast<uint64_t*>(read_registers_buf), 42,  repeat * ELEM_LINE);
        setArray(const_cast<uint64_t*>(valid_buf), 42,  repeat * ELEM_LINE);
        setArray(const_cast<uint64_t*>(finish_buf), 42,  4*ELEM_LINE);

        // Start the test
        writeTestCSR(0, 0);

<cpu_threads>

        while (42 == finish_buf[0])
        {
            nanosleep(&pause, NULL);
        }


        for(int i=0; i<repeat; i++) {
            if (valid_buf[i*ELEM_LINE]) {
                valid_traces++;
<assert_test>
            }
        }
    }
    cout<< "I had " << valid_traces << " valid traces" << endl;

//    cout << "Printing read registers" << endl;
//    printArray(const_cast<uint64_t*>(read_registers_buf), ELEM_LINE, repeat);

//    cout << "Printing valid registers" << endl;
//    printArray(const_cast<uint64_t*>(valid_buf), ELEM_LINE, repeat);


    std::chrono::high_resolution_clock::time_point time2 = std::chrono::high_resolution_clock::now();
    auto duration = std::chrono::duration_cast<std::chrono::milliseconds>( time2 - time1 ).count();


    cout << "Test took " << (duration/1000) << " seconds" << endl;
    cout << endl << endl;

    uint64_t read_cnt = readTestCSR(4);
    uint64_t write_cnt = readTestCSR(5);
    uint64_t checked_read_cnt = readTestCSR(6);


    uint64_t vl0_lines_n = readCommonCSR(CCI_TEST::CSR_COMMON_VL0_RD_LINES) +
                           readCommonCSR(CCI_TEST::CSR_COMMON_VL0_WR_LINES);
    uint64_t vh0_lines_n = readCommonCSR(CCI_TEST::CSR_COMMON_VH0_LINES);
    uint64_t vh1_lines_n = readCommonCSR(CCI_TEST::CSR_COMMON_VH1_LINES);

    uint64_t va_req_lines_n = readCommonCSR(CCI_TEST::CSR_COMMON_VA_REQ_LINES);
    uint64_t vl0_req_lines_n = readCommonCSR(CCI_TEST::CSR_COMMON_VL0_REQ_LINES);
    uint64_t vh0_req_lines_n = readCommonCSR(CCI_TEST::CSR_COMMON_VH0_REQ_LINES);
    uint64_t vh1_req_lines_n = readCommonCSR(CCI_TEST::CSR_COMMON_VH1_REQ_LINES);

    cout << "   VA REQ " << va_req_lines_n - va_req_lines
         << " : VL0 REQ " << vl0_req_lines_n - vl0_req_lines
         << " : VH0 REQ " << vh0_req_lines_n - vh0_req_lines
         << " : VH1 REQ " << vh1_req_lines_n - vh1_req_lines
         << endl;

    cout << "           "
         << "   VL0 RSP " << vl0_lines_n - vl0_lines
         << " : VH0 RSP " << vh0_lines_n - vh0_lines
         << " : VH1 RSP " << vh1_lines_n - vh1_lines
         << endl;

     // Reads CSRs to get some statistics
     cout << "#" << endl
          << "# AFU frequency: " << getAFUMHz() << " MHz"
          << (hwIsSimulated() ? " [simulated]" : "")
          << endl;
    if (!valid_test) {
      cout << "Trace was not valid";
      return 1;
    }

    // Stall the CPU so that it does not deallocate memory too soon
//    pause.tv_sec = 2;
//    nanosleep(&pause, NULL);

    return 0;
}

uint64_t
<test_name>::testNumCyclesExecuted()
{
    return totalCycles;
}
