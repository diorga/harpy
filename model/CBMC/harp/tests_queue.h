#ifndef TESTS_QUEUE_H_
#define TESTS_QUEUE_H_

#include "actors.h"

#define MAX_CPU_WRITES 5
#define MAX_CPU_READS 5
#define MAX_WR_REQ 5
#define MAX_RD_REQ 5

/*
 * x     ---> location
 * v     ---> value
 * vc    ---> virtual channel (* represents don't care)
 * mdata ---> meta data(tag)
 *
 *
 * WrReq(x, v, vc, mdata) or WrReq(x, vc, mdata) = v
 * RdReq(x, vc, mdata)
 * FnReq(vc, mdata)
 * WrRsp(mdata)
 * RdRsp(v, mdata) or v = RdRsp(mdata)
 * FnRsp(mdata)
 * CpuWrite(x,v) or CpuWrite(x) = v
 * CpuRead (x,v) or v = CpuRead(v)
 *
 * Tests inspired from Intel Acceleration Stack for Intel® Xeon® CPU with FPGAs
 * Core Cache Interface (CCI-P) Reference Manual MNL -1092 | 2019.11.04
 */

// Memory mapping
#define QUEUE_ADDR      0
#define QUEUE_SIZE      3
#define HEAD_ADDR       4
#define TAIL_ADDR       3


/*
 * Two enques by the FPGA
 * Initially: sharedMemory[0] == 0 && sharedMemory[1] == 0
 * head == 0 && tail == 0
 *
 *
 * 0:  WrReq(QUEUE_ADDR + tail, 0, mdata0) = 1
 * 1:  WrRsp(mdata0)
 * 2:  WrReq(TAIL_ADDR, 0, mdata1) = tail+1
 * 3:  WrRsp(mdata1)
 *
 * 4:  WrReq(QUEUE_ADDR + tail + 1, 0, mdata2) = 2
 * 5:  WrRsp(mdata2)
 * 6:  WrReq(TAIL_ADDR, 0, mdata3) = head + 1
 * 7:  WrRsp(mdata3)
 *
 * 8:  FnReq(0, mdata4)
 * 9:  FnRsp(mdata4)
 *
 * (sharedMemory[QUEUE_ADDR] == 1) && (sharedMemory[QUEUE_ADDR] == 2) &&
 * (sharedMemory[TAIL_ADDR] == 2)
 * Success
 */
#ifdef QUEUE_TEST_1
#define MAX_CPU_WRITES 0
#define MAX_CPU_READS 0
#define MAX_WR_REQ 5
#define MAX_RD_REQ 0
void queue_no_mpf_single_channel_FPGA_enqueue_FPGA_enqueue();
#endif


/*
 * Two deques by the FPGA
 * Initially: sharedMemory[0] == 42 && sharedMemory[1] == 43
 * head == 0 && tail == 2
 *
 * 0:  RdReq(QUEUE_ADDR + head, 0, mdata0)
 * 1:  r1 = RdRsp(mdata0)
 * 2:  WrReq(HEAD_ADDR, 0, mdata0) = head + 1
 * 3:  WrRsp(mdata0)
 *
 * 4:  RdReq(QUEUE_ADDR + head + 1, 0, mdata1)
 * 5:  r2 = RdRsp(mdata1)
 * 6:  WrReq(HEAD_ADDR, 0, mdata1) = head + 1
 * 7:  WrRsp(mdata1)
 *
 * 8:  FnReq(0, mdata2)
 * 9:  FnRsp(mdata2)
 *
 * (r1 == 1) && (r2 == 2) &&
 * (sharedMemory[HEAD_ADDR] == 2)
 * Success
 */
#ifdef QUEUE_TEST_2
#define MAX_CPU_WRITES 0
#define MAX_CPU_READS 0
#define MAX_WR_REQ 3
#define MAX_RD_REQ 2
void queue_no_mpf_single_channel_FPGA_dequeue_FPGA_dequeue();
#endif


/*
 * Enqueue by the FPGA, dequeue by the CPU
 * Initially: sharedMemory[0] == 0
 * head == 0 && tail == 0
 *
 * 0:  WrReq(QUEUE_ADDR + tail, 0, mdata0) = 42
 * 1:  WrRsp(mdata0)
 * 2:  WrReq(TAIL_ADDR, 0, mdata1) = head + 1
 * 3:  WrRsp(mdata1)
 *
 * 0:  tail = CpuRead(TAIL_ADDR) until (tail != head)
 * 1:  r1 = CpuRead(HEAD_ADDR)
 * 2:  CpuWrite(HEAD_ADDR) = head + 1
 *
 * (r1 == 42) && sharedMemory[TAIL_ADDR] == 1
 * Success
 */
#ifdef QUEUE_TEST_3
#define MAX_CPU_WRITES 1
#define MAX_CPU_READS 2
#define MAX_WR_REQ 2
#define MAX_RD_REQ 0
void queue_no_mpf_single_channel_FPGA_enqueue_CPU_dequeue();
#endif


/*
 * Enqueue by the CPU, dequeue by the FPGA
 * Initially: sharedMemory[0] == 0
 * head == 0 && tail == 0
 *
 *
 * 0:  CpuWrite(tail) = 42
 * 1:  CpuWrite(TAIL_ADDR) = tail + 1
 *
 * 0:  RdReq(TAIL_ADDR, 0, mdata0)
 * 1:  tail = RdRsp(mdata0) until (tail != head)
 * 2:  RdReq(QUEUE_ADDR + head, 0, mdata1)
 * 3:  r1 = RdRsp(mdata1)
 * 4:  WrReq(HEAD_ADDR, 0, mdata0) = head + 1
 * 5:  WrRsp(mdata0)
 *
 * (r1 == 1) && sharedMemory[TAIL_ADDR] == 1
 * Success
 */
#ifdef QUEUE_TEST_4
#define MAX_CPU_WRITES 2
#define MAX_CPU_READS 0
#define MAX_WR_REQ 1
#define MAX_RD_REQ 2
void queue_no_mpf_single_channel_CPU_enqueue_FPGA_dequeue();
#endif


/*
 * Multiple channels tests
 */


/*
 * Two enques by the FPGA
 * Initially: sharedMemory[0] == 0 && sharedMemory[1] == 0
 * head == 0 && tail == 0
 *
 * 0:  WrReq(QUEUE_ADDR + tail, VA, mdata0) = 42
 * 1:  FnReq(VA, mdata1)
 * 2:  WrReq(TAIL_ADDR, VA, mdata2) = tail + 1
 *
 * 3:  WrReq(QUEUE_ADDR + tail, VA, mdata3) = 43
 * 4:  FnRsp(mdata4)
 * 5:  WrReq(TAIL_ADDR, VA, mdata5) = tail + 2
 *
 * 6:  FnReq(VA, mdata6)
 * 7:  FnRsp(mdata6)
 *
 * (sharedMemory[QUEUE_ADDR] == 42) && (sharedMemory[QUEUE_ADDR] == 43) &&
 * (sharedMemory[TAIL_ADDR] == 2)
 * Success
 */
#ifdef QUEUE_TEST_5
#define MAX_CPU_WRITES 0
#define MAX_CPU_READS 0
#define MAX_WR_REQ 7
#define MAX_RD_REQ 0
void queue_no_mpf_multiple_channels_FPGA_enqueue_FPGA_enqueue();
#endif


/*
 * Two deques by the FPGA
 * Initially: sharedMemory[0] == 42 && sharedMemory[1] == 43
 * head == 0 && tail == 2
 *
 * 0:  RdReq(QUEUE_ADDR + head, VA, mdata0)
 * 1:  r1 = RdRsp(mdata0)
 * 2:  WrReq(HEAD_ADDR, VA, mdata0) = head + 1
 * 3:  WrRsp(mdata0)
 *
 *
 * 4:  RdReq(QUEUE_ADDR + head, VA, mdata1)
 * 5:  r2 = RdRsp(mdata1)
 * 6:  WrReq(HEAD_ADDR, VA, mdata1) = head + 1
 * 7:  WrRsp(mdata1)
 *
 * 8:  FnReq(0, mdata2)
 * 9:  FnRsp(mdata2)
 *
 * (r1 == 1) && (r2 == 2) &&
 * (sharedMemory[HEAD_ADDR] == 2)
 * Success
 */
#ifdef QUEUE_TEST_6
#define MAX_CPU_WRITES 0
#define MAX_CPU_READS 0
#define MAX_WR_REQ 3
#define MAX_RD_REQ 2
void queue_no_mpf_multiple_channels_FPGA_dequeue_FPGA_dequeue();
#endif


/*
 * Enqueue by the FPGA, dequeue by the CPU
 * Initially: sharedMemory[0] == 0 && sharedMemory[1] == 0
 * head == 0 && tail == 0
 *
 * 0:  WrReq(QUEUE_ADDR + tail, VA, mdata0) = 42
 * 1:  FnReq(VA, mdata1)
 * 2:  WrReq(TAIL_ADDR, VA, mdata1) = tail + 1
 *
 * 0:  tail = CpuRead(TAIL_ADDR) until tail!=head
 * 1:  r1 = CpuRead(HEAD_ADDR)
 * 2:  CpuWrite(HEAD_ADDR) = head + 1
 *
 * (r1 == 42)
 * Success
 */
#ifdef QUEUE_TEST_7
#define MAX_CPU_WRITES 1
#define MAX_CPU_READS 2
#define MAX_WR_REQ 3
#define MAX_RD_REQ 0
void queue_no_mpf_multiple_channels_FPGA_enqueue_CPU_dequeue();
#endif


/*
 * Enqueue by the CPU, dequeue by the FPGA
 * Initially: sharedMemory[0] == 0 && sharedMemory[1] == 0
 * head == 0 && tail == 0
 *
 *
 * 0:  CpuWrite(tail) = 1
 * 1:  CpuWrite(TAIL_ADDR) = tail + 1
 *
 * 0:  RdReq(TAIL_ADDR, VA, mdata0)
 * 1:  tail = RdRsp(mdata0)
 * 2:  RdReq(QUEUE_ADDR + head, VA, mdata1)
 * 3:  r1 = RdRsp(mdata1)
 * 4:  WrReq(HEAD_ADDR, VA, mdata0) = head + 1
 * 5:  WrRsp(mdata0)
 *
 * 6:  FnReq(VA, mdata1)
 * 7:  FnRsp(mdata1)
 *
 * (r1 == 1) && sharedMemory[TAIL_ADDR] == 1
 * Success
 */
#ifdef QUEUE_TEST_8
#define MAX_CPU_WRITES 2
#define MAX_CPU_READS 0
#define MAX_WR_REQ 1
#define MAX_RD_REQ 2
void queue_no_mpf_multiple_channels_CPU_enqueue_FPGA_dequeue();
#endif



#endif /* tests_QUEUE_H_ */
