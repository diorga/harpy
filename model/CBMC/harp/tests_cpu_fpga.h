#ifndef TESTS_CPU_FPGA_H_
#define TESTS_CPU_FPGA_H_

#include "actors.h"


/*
 * x     ---> location
 * v     ---> value
 * vc    ---> virtual channel (VA represents don't care)
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


/*
 *
 * Taken from Table 34, page 40
 * Two Writes to Same VC, Only One Outstanding
 *
 * Also suggested by example 2 (top of page), page 43
 *
 * WrReq(x, ch, mdata1) = 1          | r1 = CpuRead(x)
 * WrRsp(ch, mdata1)                 | r2 = CpuRead(x)
 *                                   |
 * WrReq(x, ch, mdata2) = 2          |
 * WrRsp(ch, mdata2)                 |
 *
 *
 * !(r1 == 2 && r2 == 1)
 * Success
 */
#ifdef FPGA_CPU_TEST_1
#define MAX_WR_REQ 2
#define MAX_RD_REQ 0
#define MAX_CPU_WRITES 0
#define MAX_CPU_READS 2
void fpga_2writes_cpu_2reads_same_channel_with_response();
#endif


/*
 *
 * A modification of the test from Table 34, page 40
 *
 * Also suggested by example 2 (top of page), page 43
 *
 * WrReq(x, *, mdata1) = 1          | r1 = CpuRead(x)
 * WrRsp(*, mdata1)                 | r2 = CpuRead(x)
 *                                  |
 * WrReq(x, *, mdata2) = 2          |
 * WrRsp(*, mdata2)                 |
 *
 *
 * !(r1 ==2 && r2 == 1)
 * Fail
 */
#ifdef FPGA_CPU_TEST_2
#define MAX_WR_REQ 2
#define MAX_RD_REQ 0
#define MAX_CPU_WRITES 0
#define MAX_CPU_READS 2
void fpga_2writes_cpu_2reads_any_channel_with_response();
#endif


/*
 *
 * Test from Table 35, page 41
 * Write Out of Order Commit
 *
 * Also suggested by example 2 (top of page), page 43
 *
 * WrReq(x, 0, mdata1) = 1          | r1 = CpuRead(x)
 *                                  | r2 = CpuRead(x)
 * WrReq(x, 1, mdata2) = 2          |
 *
 *
 * !(r1 ==2 && r2 == 1)
 * Fail
 */
#ifdef FPGA_CPU_TEST_3
#define MAX_WR_REQ 2
#define MAX_RD_REQ 0
#define MAX_CPU_WRITES 0
#define MAX_CPU_READS 2
void fpga_2writes_cpu_2reads_different_channel_no_sync();
#endif


/*
 *
 * Taken from Table 36, page 41
 * Use WrFence to Enforce Write Ordering
 *
 * Also suggested by example 2 (top of page), page 43
 *
 * WrReq(x, *, mdata1) = 1          | r1 = CpuRead(x)
 *                                  | r2 = CpuRead(x)
 * WrFence(*, mdata)                |
 *                                  |
 * WrReq(x, *, mdata2) = 2          |
 *
 *
 * !(r1 ==2 && r2 == 1)
 * Success
 */
#ifdef FPGA_CPU_TEST_4
#define MAX_WR_REQ 3
#define MAX_RD_REQ 0
#define MAX_CPU_WRITES 0
#define MAX_CPU_READS 2
void fpga_2writes_cpu_2reads_any_channel_with_fence();
#endif

/*
 *
 * Taken from Table 37, page 41
 * Read Re-Ordering to Same Address, different VCs
 *
 *
 * RdReq(x, vc1, mdata1)          | CpuWrite(x) = 1
 * RdReq(x, vc2, mdata2)          | CpuWrite(x) = 2
 * r1 = RdRsp(vc2, mdata2)        |
 * r2 = RdRsp(vc1, mdata1)        |
 *
 *
 *
 * !(r1 ==2 && r2 == 1)
 * Fail
 */
#ifdef FPGA_CPU_TEST_5
#define MAX_WR_REQ 0
#define MAX_RD_REQ 2
#define MAX_CPU_WRITES 2
#define MAX_CPU_READS 0
void fpga_2reads_cpu_2writes_different_channel_no_sync();
#endif

/*
 *
 * Taken from Table 37, page 41
 * Read Re-Ordering to Same Address, different VCs
 *
 *
 * RdReq(x, vc, mdata1)           | CpuWrite(x) = 1
 * RdReq(x, vc, mdata2)           | CpuWrite(x) = 2
 * r1 = RdRsp(vc2, mdata2)        |
 * r2 = RdRsp(vc1, mdata1)        |
 *
 *
 *
 * (r1 ==1 && r2 == 2)
 * Success
 */
#ifdef FPGA_CPU_TEST_6
#define MAX_WR_REQ 0
#define MAX_RD_REQ 2
#define MAX_CPU_WRITES 2
#define MAX_CPU_READS 0
void fpga_2reads_cpu_2writes_same_channel_no_sync();
#endif


#endif /* tests_CPU_FPGA_H_ */
