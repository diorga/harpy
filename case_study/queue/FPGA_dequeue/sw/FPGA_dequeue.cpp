#include "FPGA_dequeue.h"
// Generated from the AFU JSON file by afu_json_mgr
#include "afu_json_info.h"

#include <unistd.h>
#include <time.h>
#include <boost/format.hpp>
#include <boost/algorithm/string.hpp>
#include <stdlib.h>
#include <sys/mman.h>
#include <chrono>

#include "common.h"

#define ELEM_LINE   8
#define BUFFER_SIZE 32

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
      ("rdline-mode", po::value<string>()->default_value("S"), "Emit read requests with mode (I [invalid], S [shared])")
      ("rdline-channel", po::value<string>()->default_value("VA"), "Emit read requests on channel (VA [automatic], VL0 [QPI], VH0 [PCIe0], VH1 [PCIe1])")
      ("wrline-mode", po::value<string>()->default_value("M"), "Emit write requests with mode (I [invalid], M [modified], or P [push])")
      ("wrline-channel", po::value<string>()->default_value("VA"), "Emit write requests on channel (VA [automatic], VL0 [QPI], VH0 [PCIe0], VH1 [PCIe1])")
      ("fence", po::value<bool>()->default_value(false), "Enable fence ")
      ("fence_rsp", po::value<bool>()->default_value(false), "Enable fence response")
      ("wr_rsp_write_head", po::value<bool>()->default_value(true), "Enable write response write head")
      ("elements,e", po::value<int>()->default_value(100), "The total nuber of elements to enqueue/dequeue")
      ("VL0_enemy", po::value<int>()->default_value(0), "Activate a VL0 enemy, a higher number coresponds to a higher frequency")
      ("VH0_enemy", po::value<int>()->default_value(0), "Activate a VH0 enemy, a higher number coresponds to a higher frequency")
      ("VH1_enemy", po::value<int>()->default_value(0), "Activate a VH1 enemy, a higher number coresponds to a higher frequency")
      ;

}

CCI_TEST* allocTest(const po::variables_map& vm, SVC_WRAPPER& svc)
{
    return new FPGA_dequeue(vm, svc);
}



// ========================================================================
//
// Coherance write after read.
//
// ========================================================================

int FPGA_dequeue::test()
{

    uint64_t elements = uint64_t(vm["elements"].as<int>());
    uint64_t fence = (vm["fence"].as<bool>() ? 1 : 0);
    uint64_t fence_rsp = (vm["fence_rsp"].as<bool>() ? 1 : 0);
    uint64_t wr_rsp_write_head = (vm["wr_rsp_write_head"].as<bool>() ? 1 : 0);

    uint64_t VL0_enemy = uint64_t(vm["VL0_enemy"].as<int>());
    uint64_t VH0_enemy = uint64_t(vm["VH0_enemy"].as<int>());
    uint64_t VH1_enemy = uint64_t(vm["VH1_enemy"].as<int>());

    uint64_t head = 0;
    uint64_t tail = 0;


    // Alocate memory for the queue
    auto queue_handle = this->allocBuffer( BUFFER_SIZE * ELEM_LINE * sizeof(uint64_t) );
    auto queue = reinterpret_cast<volatile uint64_t*>(queue_handle->c_type());
    assert(NULL != queue);
    // Initialize the x linked list in the buffer
    setArray(const_cast<uint64_t*>(queue), 0, BUFFER_SIZE * ELEM_LINE);


    // Alocate memory for the head and tail
    auto head_tail_handle = this->allocBuffer( 4 * ELEM_LINE * sizeof(uint64_t) );
    auto head_tail = reinterpret_cast<volatile uint64_t*>(head_tail_handle->c_type());
    assert(NULL != head_tail);
    // Initialize the x linked list in the buffer
    setArray(const_cast<uint64_t*>(head_tail), 0, 4 * ELEM_LINE);


    // Alocate memory for final space
    auto back_handle = this->allocBuffer( elements * ELEM_LINE * sizeof(uint64_t) );
    auto back = reinterpret_cast<volatile uint64_t*>(back_handle->c_type());
    assert(NULL != back);
    // Initialize the final
    setArray(const_cast<uint64_t*>(back), 0, elements * ELEM_LINE);


    //
    // Configure the HW test
    //
    writeTestCSR(1, intptr_t(queue));
    writeTestCSR(2, intptr_t(head_tail));
    writeTestCSR(3, intptr_t(back));


    uint64_t rdline_mode;
    switch (toupper(vm["rdline-mode"].as<string>()[0]))
    {
      case 'I':
        rdline_mode = 0;
        break;
      case 'S':
        rdline_mode = 1;
        break;
      default:
        cerr << "Invalid --rdline-mode.  Expected I or S." << endl;
        exit(1);
    }

    auto  r_channel = vm["rdline-channel"].as<string>();
    uint64_t rdline_channel;

    if (boost::iequals(r_channel, "VA")) { rdline_channel = 0; }
    else if (boost::iequals(r_channel, "VL0")) { rdline_channel = 1; }
    else if (boost::iequals(r_channel, "VH0")) { rdline_channel = 2; }
    else if (boost::iequals(r_channel, "VH1")) { rdline_channel = 3; }
    else
    {
        cerr << "Invalid --rdline-channel  Expected VA, VL0, VH0 or VH1." << endl;
        exit(1);
    }


    uint64_t wrline_mode;
    switch (toupper(vm["wrline-mode"].as<string>()[0]))
    {
      case 'I':
        wrline_mode = 0;
        break;
      case 'M':
        wrline_mode = 1;
        break;
      case 'P':
        wrline_mode = 2;
        break;
      default:
        cerr << "Invalid --wrline-mode.  Expected I, M or P." << endl;
        exit(1);
    }

    auto w_channel = vm["wrline-channel"].as<string>();
    uint64_t wrline_channel;


    if (boost::iequals(w_channel, "VA")) { wrline_channel = 0; }
    else if (boost::iequals(w_channel, "VL0")) { wrline_channel = 1; }
    else if (boost::iequals(w_channel, "VH0")) { wrline_channel = 2; }
    else if (boost::iequals(w_channel, "VH1")) { wrline_channel = 3; }
    else
    {
        cerr << "Invalid --wtline-channel  Expected VA, VL0, VH0 or VH1." << endl;
        exit(1);
    }

    uint64_t vl0_lines = readCommonCSR(CCI_TEST::CSR_COMMON_VL0_RD_LINES) +
                         readCommonCSR(CCI_TEST::CSR_COMMON_VL0_WR_LINES);
    uint64_t vh0_lines = readCommonCSR(CCI_TEST::CSR_COMMON_VH0_LINES);
    uint64_t vh1_lines = readCommonCSR(CCI_TEST::CSR_COMMON_VH1_LINES);


    writeTestCSR(4, elements);

    writeTestCSR(5, VL0_enemy);

    writeTestCSR(6, VH0_enemy);

    writeTestCSR(7, VH1_enemy);

    // Start the test
    std::chrono::high_resolution_clock::time_point t1 = std::chrono::high_resolution_clock::now();
    writeTestCSR(0,
                 (wrline_channel << 8) |
                 (wrline_mode << 6) |
                 (rdline_channel << 4) |
                 (rdline_mode << 3) |
                 (fence_rsp << 2) |
                 (fence << 1) |
                 (wr_rsp_write_head) );

    cout << "Queue address " << hex << intptr_t(queue) << endl;
    cout << "Head and tail address " << hex << intptr_t(head_tail)  << endl << endl;
    cout << "Tail at " << hex << intptr_t(&head_tail[ELEM_LINE])  << endl << endl;

    cout << "Streaming  " << dec << elements << "elements" << endl;
    cout << "wrline_mode " << dec << wrline_mode << endl;
    cout << "rdline_mode " << dec << rdline_mode << endl;
    cout << "fence " << dec << fence << endl;

    struct timespec pause;
    // Longer when simulating
    pause.tv_sec = (hwIsSimulated() ? 1 : 0);
    pause.tv_nsec = 2500000;

    cout << endl << "Started streaming elements" << endl;

    int sent = 0;

    while(0 == head_tail[2*ELEM_LINE])
    {
        while (sent < elements)
        {
            head = head_tail[0]; // Read head
            if (((tail + 1) % BUFFER_SIZE) != head) //If not full
            {
                queue[tail*ELEM_LINE] = sent;
                std::atomic_thread_fence(std::memory_order_seq_cst);
                tail = (head_tail[ELEM_LINE] + 1) % BUFFER_SIZE;
                head_tail[ELEM_LINE] = tail;
                std::atomic_thread_fence(std::memory_order_seq_cst);
                sent++;
//                cout<<" Tail is"<<tail<<endl;
//                cout<<" Head is"<<head<<endl;
            } else {
//                nanosleep(&pause, NULL);
            }
        }
    }

    std::chrono::high_resolution_clock::time_point t2 = std::chrono::high_resolution_clock::now();
    auto duration = std::chrono::duration_cast<std::chrono::milliseconds>( t2 - t1 ).count();

    cout << "Test took " << duration << " miliseconds" << endl;
    cout << endl << endl;

    nanosleep(&pause, NULL);
    int wrong_entries = 0;
    int reorderings = 0;
    for(int i=0; i<elements; i++) {
        if (i != back[i*ELEM_LINE]) {
          wrong_entries++;
          int seen_before = 0;
          for(int j=0; j<i; j=j++) {
            if (back[i*ELEM_LINE] == back[j*ELEM_LINE]) seen_before = 1;
          }
          if (!seen_before) reorderings++;
        }
//       cout << back[i * ELEM_LINE] << " ";
    }
    cout << endl;
    cout << "Number of wrong entries " << wrong_entries << endl;
    cout << "Number of reorderings " << reorderings << endl <<endl;


    uint64_t read_cnt = readTestCSR(4);
    uint64_t write_cnt = readTestCSR(5);
    uint64_t checked_read_cnt = readTestCSR(6);


    uint64_t vl0_lines_n = readCommonCSR(CCI_TEST::CSR_COMMON_VL0_RD_LINES) +
                           readCommonCSR(CCI_TEST::CSR_COMMON_VL0_WR_LINES);
    uint64_t vh0_lines_n = readCommonCSR(CCI_TEST::CSR_COMMON_VH0_LINES);
    uint64_t vh1_lines_n = readCommonCSR(CCI_TEST::CSR_COMMON_VH1_LINES);

    cout << "   VL0 " << vl0_lines_n - vl0_lines
         << " : VH0 " << vh0_lines_n - vh0_lines
         << " : VH1 " << vh1_lines_n - vh1_lines
         << endl;

     // Reads CSRs to get some statistics
     cout << "#" << endl
          << "# AFU frequency: " << getAFUMHz() << " MHz"
          << (hwIsSimulated() ? " [simulated]" : "")
          << endl;

    // Stall the CPU so that it does not deallocate memory too soon
    pause.tv_sec = 2;
    nanosleep(&pause, NULL);

    return 0;
}

uint64_t
FPGA_dequeue::testNumCyclesExecuted()
{
    return totalCycles;
}
