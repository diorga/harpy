#include "FPGA_enqueue.h"
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
      ("wr_rsp_enqueue", po::value<bool>()->default_value(true), "Enable write response enqueue")
      ("wr_rsp_write_tail", po::value<bool>()->default_value(true), "Enable write response write tail")
      ("fence1", po::value<bool>()->default_value(false), "Enable fence1 ")
      ("fence1_rsp", po::value<bool>()->default_value(false), "Enable fence1 response")
      ("fence2", po::value<bool>()->default_value(false), "Enable fence2 ")
      ("fence2_rsp", po::value<bool>()->default_value(false), "Enable fence2 response")
      ("elements,e", po::value<int>()->default_value(100), "The total nuber of elements to enqueue/dequeue")
      ("VL0_enemy", po::value<int>()->default_value(0), "Activate a VL0 enemy, a higher number coresponds to a higher frequency")
      ("VH0_enemy", po::value<int>()->default_value(0), "Activate a VH0 enemy, a higher number coresponds to a higher frequency")
      ("VH1_enemy", po::value<int>()->default_value(0), "Activate a VH1 enemy, a higher number coresponds to a higher frequency")
      ;

}

CCI_TEST* allocTest(const po::variables_map& vm, SVC_WRAPPER& svc)
{
    return new FPGA_enqueue(vm, svc);
}

void EditDistDP(uint64_t *str1, uint64_t *str2, int len1, int len2)
{

    // Create a DP array to memoize result
    // of previous computations
    int DP[2][len1 + 1];

    // To fill the DP array with 0
    memset(DP, 0, sizeof DP);

    // Base condition when second string
    // is empty then we remove all characters
    for (int i = 0; i <= len1; i++)
        DP[0][i] = i;

    // Start filling the DP
    // This loop run for every
    // character in second string
    for (int i = 1; i <= len2; i++) {
        // This loop compares the char from
        // second string with first string
        // characters
        for (int j = len1-1000; j <= len1; j++) {
            // if first string is empty then
            // we have to perform add character
            // operation to get second string
            if (j == 0)
                DP[i % 2][j] = i;

            // if character from both string
            // is same then we do not perform any
            // operation . here i % 2 is for bound
            // the row number.
            else if (str1[j - 1] == str2[i - 1]) {
                DP[i % 2][j] = DP[(i - 1) % 2][j - 1];
            }

            // if character from both string is
            // not same then we take the minimum
            // from three specified operation
            else {
                DP[i % 2][j] = 1 + min(DP[(i - 1) % 2][j],
                                       min(DP[i % 2][j - 1],
                                           DP[(i - 1) % 2][j - 1]));
            }
        }
    }

    // after complete fill the DP array
    // if the len2 is even then we end
    // up in the 0th row else we end up
    // in the 1th row so we take len2 % 2
    // to get row
    cout <<"Distance "<< DP[len2 % 2][len1] << endl;
}



// ========================================================================
//
// Coherance write after read.
//
// ========================================================================

int FPGA_enqueue::test()
{

    uint64_t elements = uint64_t(vm["elements"].as<int>());
    uint64_t wr_rsp_enqueue = (vm["wr_rsp_enqueue"].as<bool>() ? 1 : 0);
    uint64_t wr_rsp_write_tail = (vm["wr_rsp_write_tail"].as<bool>() ? 1 : 0);
    uint64_t fence1 = (vm["fence1"].as<bool>() ? 1 : 0);
    uint64_t fence1_rsp = (vm["fence1_rsp"].as<bool>() ? 1 : 0);
    uint64_t fence2 = (vm["fence2"].as<bool>() ? 1 : 0);
    uint64_t fence2_rsp = (vm["fence2_rsp"].as<bool>() ? 1 : 0);

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




    //
    // Configure the HW test
    //
    writeTestCSR(1, intptr_t(queue));
    writeTestCSR(2, intptr_t(head_tail));


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


//    writeTestCSR(3, buffer_size);
    writeTestCSR(4, elements);

    writeTestCSR(5, VL0_enemy);

    writeTestCSR(6, VH0_enemy);

    writeTestCSR(7, VH1_enemy);



//    cout << "Queue address " << hex << intptr_t(queue) << endl;
//    cout << "Head and tail address " << hex << intptr_t(head_tail)  << endl << endl;
//    cout << "Tail at " << hex << intptr_t(&head_tail[ELEM_LINE])  << endl << endl;

    cout << "Streaming  " << dec << elements << "elements" << endl;
    cout << "Fence1 " << dec << fence1 << endl;
    cout << "Fence1_rsp " << dec << fence1_rsp << endl;
    cout << "Fence2 " << dec << fence2 << endl;
    cout << "Fence2_rsp " << dec << fence2_rsp << endl;
    cout << "Write response enqueue " << dec << wr_rsp_enqueue << endl;
    cout << "Write response write tail " << dec << wr_rsp_write_tail << endl;

    cout << "wrline_mode " << dec << wrline_mode << endl;
    cout << "rdline_mode " << dec << rdline_mode << endl;

    struct timespec pause;
    // Longer when simulating
    pause.tv_sec = (hwIsSimulated() ? 1 : 0);
    pause.tv_nsec = 2500000;

    int read = 0;
    uint64_t value;
    uint64_t *read_values;
    read_values = new uint64_t[elements];

    cout << endl << "Started streaming elements" << endl;

    // Start the test
    std::chrono::high_resolution_clock::time_point t1 = std::chrono::high_resolution_clock::now();
    writeTestCSR( 0,
                  (wrline_channel << 11) |
                  (wrline_mode << 9) |
                  (rdline_channel << 7) |
                  (rdline_mode << 6) |
                  (fence2_rsp << 5) |
                  (fence2 << 4) |
                  (fence1_rsp << 3) |
                  (fence1 << 2) |
                  (wr_rsp_write_tail << 1) |
                  (wr_rsp_enqueue) );

    while((0 == head_tail[2*ELEM_LINE]) && (read < elements))
    {
            tail = head_tail[ELEM_LINE]; // Read tail
            if (tail != head) //If not empty
            {
                value = queue[head*ELEM_LINE] ;
                std::atomic_thread_fence(std::memory_order_seq_cst);
                head = (head_tail[0] + 1) % BUFFER_SIZE;
                head_tail[0] = head;
                std::atomic_thread_fence(std::memory_order_seq_cst);
                read_values[read] = value;
                read++;
//                cout<<" Tail is"<<tail<<endl;
//                cout<<" Head is"<<head<<endl;
//                cout<<" Value is"<<value<<endl;
            } else {
//                nanosleep(&pause, NULL);
            }
    }


    std::chrono::high_resolution_clock::time_point t2 = std::chrono::high_resolution_clock::now();
    auto duration = std::chrono::duration_cast<std::chrono::milliseconds>( t2 - t1 ).count();

    cout << "Test took " << duration << " miliseconds" << endl;
    cout << endl << endl;

    int wrong_entries = 0;
    uint64_t *expected_values;
    expected_values = new uint64_t[elements];
    for(int i=0; i<elements; i++) {
        if (i != read_values[i]) wrong_entries++;
        expected_values[i]=i;
    }

    cout << "Number of wrong entries " << wrong_entries << endl;
    EditDistDP(expected_values,read_values, elements, read);

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
FPGA_enqueue::testNumCyclesExecuted()
{
    return totalCycles;
}
