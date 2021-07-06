#include "actors.h"                       // Header definition for all the actors

#ifdef TESTS_FPGA
#include "tests_fpga.h"
#endif
#ifdef TESTS_CPU_FPGA
#include "tests_cpu_fpga.h"
#define ENABLE_SC_CPU1  1
#endif
#ifdef TESTS_QUEUE
#include "tests_queue.h"
#endif
#ifdef TESTS_MULTIPLE_THREADS
#include "tests_multiple_threads.h"
#define ENABLE_TSO_CPU1  1
#define ENABLE_TSO_CPU2  1
#endif
#ifdef ALLOY_TRACES
#define ENABLE_TSO_CPU1  1
#define ENABLE_TSO_CPU2  1
#include "alloy_traces.h"
#endif



typedef enum {                            // Environment actors
  STEP_RDREQPOOL,
  STEP_WRREQPOOL,
  STEP_UPSTREAM_CH,
  STEP_DOWNSTREAM_CH,
  STEP_WR_REQ,
  STEP_RD_REQ,
  STEP_CPU_READ,
  STEP_CPU_WRITE,
  STEP_CPU_FENCE,
  STEP_CPU_READ2,
  STEP_CPU_WRITE2,
  STEP_CPU_FENCE2,
  STEP_WRITE_BUFFER,
  STEP_WRITE_BUFFER2,
  STEP_NOP,
} step;

step nondet_step();                       // Generate a non-det step


/*
 * FPGA System Variables
 */

ReqPool         wrReqPool;                          // The write request pool.
ReqPool         rdReqPool;                          // The read request pool
Channel         upstreamChannels[MAX_CHANNELS];     // An array of channels
Channel         downstreamChannels[MAX_CHANNELS];   // An array of channels
unsigned char   sharedMemory[MAX_LOC] = {0};        // The shared memory



/*
 * CPU System Variables
*/
WrBuffer        wrBuffer1;                          // The CPU write buffer
WrBuffer        wrBuffer2;                          // The CPU write buffer



int main() {

  /*
   * Start state
   */

  initGlobalHistory();
  initPool(&wrReqPool);
  initPool(&rdReqPool);
  for(int i=0; i<MAX_CHANNELS; i++) initChannel(&upstreamChannels[i]);
  for(int i=0; i<MAX_CHANNELS; i++) initChannel(&downstreamChannels[i]);
  initWriteBuffer(&wrBuffer1);
  initWriteBuffer(&wrBuffer2);
#ifdef TESTS_QUEUE
#ifdef QUEUE_TEST_2
  sharedMemory[QUEUE_ADDR] = 42;
  sharedMemory[QUEUE_ADDR + 1] = 43;
  sharedMemory[TAIL_ADDR] = 0;
  sharedMemory[HEAD_ADDR] = 2;
#endif
#ifdef QUEUE_TEST_6
  sharedMemory[QUEUE_ADDR] = 42;
  sharedMemory[QUEUE_ADDR + 1] = 43;
  sharedMemory[TAIL_ADDR] = 0;
  sharedMemory[HEAD_ADDR] = 2;
#endif
#endif

#ifdef TESTS_QUEUE
#if defined(QUEUE_TEST_3) || defined(QUEUE_TEST_4) || defined(QUEUE_TEST_7) || defined(QUEUE_TEST_8)
#define ENABLE_CPU               1
#endif
#endif
  /*
   * Main simulation
   */
  unsigned char ch_index;

  // Loop for a non-det ammount of simulation steps.
  for (; nondet_int();) {
    // The environment takes a step
    switch (nondet_step()) {
      case STEP_WRREQPOOL: // wrReqPool takes a step
        // Guard: at least one operation in the wrReqPool
        __CPROVER_assume(wrReqPool.num_pending_operations > 0);
        stepWrReqPool(&wrReqPool, upstreamChannels, downstreamChannels, sharedMemory);
        break;
      case STEP_RDREQPOOL:   // RdReqPool takes a step
        // Guard: at least one operation in the rdReqPool
        __CPROVER_assume(rdReqPool.num_pending_operations > 0);
        stepRdReqPool(&rdReqPool, upstreamChannels, sharedMemory);
        break;
      case STEP_UPSTREAM_CH: // One upsteam channel takes a step
        // Choose a channel non-deterministically
        ch_index = nondet_uchar();
        __CPROVER_assume( (ch_index >= 0) && (ch_index < MAX_CHANNELS));

        // Guard: channel has an element to fire
        __CPROVER_assume(upstreamChannels[ch_index].num_pending_operations > 0);
        stepUpstreamChannel(upstreamChannels, downstreamChannels, ch_index, sharedMemory);
        break;
      case STEP_DOWNSTREAM_CH: // One downstream channel takes a step
        // Choose a channel non-deterministically
        ch_index = nondet_uchar();
        __CPROVER_assume( (ch_index >= 0) && (ch_index < MAX_CHANNELS));

        // Guard: channel has an element to fire
        __CPROVER_assume(downstreamChannels[ch_index].num_pending_operations > 0);
        stepDownstreamChannel(downstreamChannels, ch_index, sharedMemory);
        break;
      case STEP_WR_REQ:
        // Guard: Write pool is not full &&
        //        Not reached max number of FPGA write requests
        __CPROVER_assume(wrReqPool.num_pending_operations < POOL_SIZE);
        __CPROVER_assume(wrReq_issued < MAX_WR_REQ);
        addToWrReqPool(&wrReqPool);
        break;
      case STEP_RD_REQ:
        // Guard: Read pool is not full &&
        //        Not reached max number of FPGA read requests
        __CPROVER_assume(rdReqPool.num_pending_operations < POOL_SIZE);
        __CPROVER_assume(rdReq_issued < MAX_RD_REQ);
        addToRdReqPool(&rdReqPool);
        break;
/*      case STEP_NOP:
        // Guard: No guard
        addNop();
        break;*/
#if ENABLE_TSO_CPU1
      case STEP_CPU_WRITE:
        // Guard: Write buffer is not full &&
        //        Not reached max number of CPU writes
        __CPROVER_assume(wrBuffer1.num_pending_operations < W_BUFFER_SIZE);
        __CPROVER_assume(cpuWrites_issued < MAX_CPU_WRITES);
        tso_core_write(&wrBuffer1, 0);
        break;
      case STEP_CPU_FENCE:
        // Guard: Not reached max number of CPU fences
        __CPROVER_assume(cpuWrites_issued < MAX_CPU_WRITES);
        tso_core_fence(&wrBuffer1, 0);
        break;
      case STEP_CPU_READ:
        // Guard: Not reached max number of CPU read requests
        __CPROVER_assume(cpuReads_issued < MAX_CPU_READS);
        tso_core_read(&wrBuffer1, sharedMemory, 0);
        break;
      case STEP_WRITE_BUFFER: // Write buffer takes a step
        // Guard: Write buffer has an element to fire
        __CPROVER_assume(wrBuffer1.num_pending_operations > 0);
        stepWriteBuffer(&wrBuffer1, sharedMemory);
        break;
#endif
#if ENABLE_TSO_CPU2
      case STEP_CPU_WRITE2:
        // Guard: Write buffer is not full &&
        //        Not reached max number of CPU write requests
        __CPROVER_assume(wrBuffer2.num_pending_operations < W_BUFFER_SIZE);
        __CPROVER_assume(cpuWrites_issued < MAX_CPU_WRITES);
        tso_core_write(&wrBuffer2, 1);
        break;
      case STEP_CPU_FENCE2:
        // Guard: Not reached max number of CPU fences
        __CPROVER_assume(cpuWrites_issued < MAX_CPU_WRITES);
        tso_core_fence(&wrBuffer2, 1);
        break;
      case STEP_CPU_READ2:
        // Guard: Not reached max number of CPU read requests
        __CPROVER_assume(cpuReads_issued < MAX_CPU_READS);
        tso_core_read(&wrBuffer2, sharedMemory, 1);
        break;
      case STEP_WRITE_BUFFER2: // Write buffer takes a step
        // Guard: Write buffer has an element to fire
        __CPROVER_assume(wrBuffer2.num_pending_operations > 0);
        stepWriteBuffer(&wrBuffer2, sharedMemory);
        break;
#endif
#if ENABLE_SC_CPU1
      case STEP_CPU_WRITE:
        // Guard: Write buffer is not full &&
        //        Not reached max number of CPU write requests
        __CPROVER_assume(cpuWrites_issued < MAX_CPU_WRITES);
        sc_core_write(sharedMemory, 0);
        break;
      case STEP_CPU_READ:
        // Guard: Not reached max number of CPU read requests
        __CPROVER_assume(cpuReads_issued < MAX_CPU_READS);
        sc_core_read(sharedMemory, 0);
        break;
#endif
#if ENABLE_SC_CPU2
      case STEP_CPU_WRITE2:
        // Guard: Write buffer is not full &&
        //        Not reached max number of CPU write requests
        __CPROVER_assume(cpuWrites_issued < MAX_CPU_WRITES);
        sc_core_write(sharedMemory, 1);
        break;
      case STEP_CPU_READ2:
        // Guard: Not reached max number of CPU read requests
        __CPROVER_assume(cpuReads_issued < MAX_CPU_READS);
        sc_core_read(sharedMemory, 1);
        break;
#endif
      default:
        // Disallow any other choices for the guarded command.
        __CPROVER_assume(0);
        break;
      }
    }


  /*
   * Check some FPGA only properties
  */

#ifdef TESTS_FPGA
if (nondet_int()) {
#ifdef FPGA_TEST_1
    one_write_one_read_any_channel_with_response();
#endif
  } else if (nondet_int()) {
#ifdef FPGA_TEST_2
    one_write_one_read_same_channel_with_response();
#endif
  } else if (nondet_int()) {
#ifdef FPGA_TEST_3
    one_write_one_read_any_channel_with_fence();
#endif
  } else if (nondet_int()) {
#ifdef FPGA_TEST_4
    two_writes_two_reads_same_channel_with_response();
#endif
  } else if (nondet_int()) {
#ifdef FPGA_TEST_5
    two_writes_two_reads_any_channel_with_response();
#endif
  } else if (nondet_int()) {
#ifdef FPGA_TEST_6
    two_writes_two_reads_different_channel_no_sync();
#endif
  } else if (nondet_int()) {
#ifdef FPGA_TEST_7
    two_writes_two_reads_any_channel_with_fence();
#endif
  } else if (nondet_int()) {
#ifdef FPGA_TEST_8
    two_writes_one_read_same_channel_no_sync();
#endif
  } else if (nondet_int()) {
#ifdef FPGA_TEST_9
    two_writes_one_read_same_channel_with_response();
#endif
  } else if (nondet_int()) {
#ifdef FPGA_TEST_10
    two_writes_one_read_same_channel_with_fence();
#endif
  } else if (nondet_int()) {
#ifdef FPGA_TEST_11
    one_read_one_write_any_channel_no_sync();
#endif
  }
#endif


  /*
   * Check some CPU-FPGA only properties
  */

#ifdef TESTS_CPU_FPGA
  if (nondet_int()) {
#ifdef FPGA_CPU_TEST_1
    fpga_2writes_cpu_2reads_same_channel_with_response();
#endif
} else if (nondet_int()) {
#ifdef FPGA_CPU_TEST_2
    fpga_2writes_cpu_2reads_any_channel_with_response();
#endif
} else if (nondet_int()) {
#ifdef FPGA_CPU_TEST_3
    fpga_2writes_cpu_2reads_different_channel_no_sync();
#endif
} else if (nondet_int()) {
#ifdef FPGA_CPU_TEST_4
    fpga_2writes_cpu_2reads_any_channel_with_fence();
#endif
} else if (nondet_int()) {
#ifdef FPGA_CPU_TEST_5
    fpga_2reads_cpu_2writes_different_channel_no_sync();
#endif
} else if (nondet_int()) {
#ifdef FPGA_CPU_TEST_6
    fpga_2reads_cpu_2writes_same_channel_no_sync();
#endif
}
#endif

#ifdef TESTS_QUEUE
  if (nondet_int()) {
#ifdef QUEUE_TEST_1
      queue_no_mpf_single_channel_FPGA_enqueue_FPGA_enqueue();
#endif
  } else if (nondet_int()) {
#ifdef QUEUE_TEST_2
      queue_no_mpf_single_channel_FPGA_dequeue_FPGA_dequeue();
#endif
  } else if (nondet_int()) {
#ifdef QUEUE_TEST_3
      queue_no_mpf_single_channel_FPGA_enqueue_CPU_dequeue();
#endif
  } else if (nondet_int()) {
#ifdef QUEUE_TEST_4
      queue_no_mpf_single_channel_CPU_enqueue_FPGA_dequeue();
#endif
  } else if (nondet_int()) {
#ifdef QUEUE_TEST_5
      queue_no_mpf_multiple_channels_FPGA_enqueue_FPGA_enqueue();
#endif
  } else if (nondet_int()) {
#ifdef QUEUE_TEST_6
      queue_no_mpf_multiple_channels_FPGA_dequeue_FPGA_dequeue();
#endif
  } else if (nondet_int()) {
#ifdef QUEUE_TEST_7
      queue_no_mpf_multiple_channels_FPGA_enqueue_CPU_dequeue();
#endif
  } else if (nondet_int()) {
#ifdef QUEUE_TEST_8
      queue_no_mpf_multiple_channels_CPU_enqueue_FPGA_dequeue();
#endif
  }
#endif

#ifdef TESTS_MULTIPLE_THREADS
  if (nondet_int()) {
#ifdef JOHN_EXAMPLE
    john_example();
#endif
  } else if (nondet_int()) {
#ifdef STORE_BUFFERING
    store_buffering();
#endif
  } else if (nondet_int()) {
#ifdef STORE_BUFFERING_FENCE
    store_buffering_fence();
#endif
  }
#endif

#ifdef ALLOY_TRACES
  alloy_traces();
#endif

  return 0;

}
