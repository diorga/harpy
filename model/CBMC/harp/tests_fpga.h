#ifndef TESTS_FPGA_H_
#define TESTS_FPGA_H_

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
 *
 *
 * Tests inspired from Intel Acceleration Stack for Intel® Xeon® CPU with FPGAs
 * Core Cache Interface (CCI-P) Reference Manual MNL -1092 | 2019.11.04
 */



/*
 * Suggested by example 3 (top of page), page 43
 *
 * WrReq(x, VA, mdata) = 1
 * WrRsp(mdata)
 *
 * RdReq(x, VA, mdata)
 * r1 = RdRsp( mdata)
 *
 *
 * !(r1 == 0)
 * Fail
 */
#ifdef FPGA_TEST_1
#define MAX_CPU_WRITES 0
#define MAX_CPU_READS 0
#define MAX_WR_REQ 1
#define MAX_RD_REQ 1
void one_write_one_read_any_channel_with_response();
#endif


/*
 * Suggested by example 3 (top of page), page 43
 *
 * WrReq(x, ch, mdata) = 1
 * WrRsp(mdata)
 *
 * RdReq(x, ch, mdata)
 * r1 = RdRsp(mdata)
 *
 *
 * !(r1 == 0)
 *
 * Success
 */
#ifdef FPGA_TEST_2
#define MAX_CPU_WRITES 0
#define MAX_CPU_READS 0
#define MAX_WR_REQ 1
#define MAX_RD_REQ 1
void one_write_one_read_same_channel_with_response();
#endif


/*
 * Suggested by example 3 (top of page), page 43
 *
 * WrReq(x, VA, mdata) = 1
 * WrRsp(mdata)
 *
 * FnReq(VA, mdata)
 * FnRsp(mdata)
 *
 * RdReq(x, VA, mdata)
 * r1 = RdRsp(mdata)
 *
 *
 * !(r1 == 0)
 * Success
 */
#ifdef FPGA_TEST_3
#define MAX_CPU_WRITES 0
#define MAX_CPU_READS 0
#define MAX_WR_REQ 2
#define MAX_RD_REQ 1
void one_write_one_read_any_channel_with_fence();
#endif


/*
 *
 * Taken from Table 34, page 40
 * Two Writes to Same VC, Only One Outstanding
 *
 * Also suggested by example 2 (top of page), page 43
 *
 * WrReq(x, ch, mdata1) = 1
 * WrRsp(mdata1)
 *
 * WrReq(x, ch, mdata2) = 2
 * WrRsp(mdata2)
 *
 * RdReq(x, ch, mdata1)
 * r1 = RdRsp(mdata1)
 *
 * RdReq(x, ch, mdata1)
 * r2 = RdRsp(mdata1)
 *
 * !(r1 == 2 && r2 == 1)
 * Success
 */
#ifdef FPGA_TEST_4
#define MAX_CPU_WRITES 0
#define MAX_CPU_READS 0
#define MAX_WR_REQ 2
#define MAX_RD_REQ 2
void two_writes_two_reads_same_channel_with_response();
#endif


/*
 *
 * A modification of the test from Table 34, page 40
 *
 * Also suggested by example 2 (top of page), page 43
 *
 * WrReq(x, VA, mdata1) = 1
 * WrRsp(mdata1)
 *
 * WrReq(x, VA, mdata2) = 2
 * WrRsp(mdata2)
 *
 * RdReq(x, VA, mdata1)
 * r1 = RdRsp(mdata1)
 *
 * RdReq(x, VA, mdata2)
 * r2 = RdRsp(mdata2)
 *
 * !(r1 ==2 && r2 == 1)
 * Fail
 */
#ifdef FPGA_TEST_5
#define MAX_CPU_WRITES 0
#define MAX_CPU_READS 0
#define MAX_WR_REQ 2
#define MAX_RD_REQ 2
void two_writes_two_reads_any_channel_with_response();
#endif


/*
 *
 * Test from Table 35, page 41
 * Write Out of Order Commit
 *
 * Also suggested by example 2 (top of page), page 43
 *
 * WrReq(x, 0, mdata1) = 1
 *
 * WrReq(x, 1, mdata2) = 2
 *
 * RdReq(x, *, mdata1)
 * r1 = RdRsp(mdata1)
 *
 * RdReq(x, VA, mdata2)
 * r2 = RdRsp(mdata2)
 *
 * !(r1 ==2 && r2 == 1)
 * Fail
 */
#ifdef FPGA_TEST_6
#define MAX_CPU_WRITES 0
#define MAX_CPU_READS 0
#define MAX_WR_REQ 2
#define MAX_RD_REQ 2
void two_writes_two_reads_different_channel_no_sync();
#endif


/*
 *
 * Taken from Table 36, page 41
 * Use WrFence to Enforce Write Ordering
 *
 * Also suggested by example 2 (top of page), page 43
 *
 * WrReq(x, VA, mdata1) = 1
 *
 * WrFence(VA, mdata)
 *
 * WrReq(x, VA, mdata2) = 2
 *
 * RdReq(x, VA, mdata1)
 * r1 = RdRsp(mdata1)
 *
 * RdReq(x, VA, mdata2)
 * r2 = RdRsp(mdata2)
 *
 * !(r1 ==2 && r2 == 1)
 * Success
 */
#ifdef FPGA_TEST_7
#define MAX_CPU_WRITES 0
#define MAX_CPU_READS 0
#define MAX_WR_REQ 3
#define MAX_RD_REQ 2
void two_writes_two_reads_any_channel_with_fence();
#endif


/*
 * Based on Example 1 (top of page), page 43
 *
 * WrReq(x, 1, mdata1) = 1
 * WrReq(x, 1 ,mdata2) = 2
 *
 * RdReq(x, 1, mdata)
 * r1 = RdRsp( mdata)
 *
 *
 * !(r1 == 1)
 *
 * Fails
 */
#ifdef FPGA_TEST_8
#define MAX_CPU_WRITES 0
#define MAX_CPU_READS 0
#define MAX_WR_REQ 2
#define MAX_RD_REQ 1
void two_writes_one_read_same_channel_no_sync();
#endif


/*
 * Based on Example 1 (top of page), page 43 - with response
 *
 * WrReq(x, 1, mdata1) = 1
 * WrRsp(mdata1)
 * WrReq(x, 1 ,mdata2) = 2
 * WrRsp(mdata2)
 *
 * RdReq(x, 1, mdata)
 * r1 = RdRsp(mdata)
 *
 *
 * (r1 == 2)
 *
 * Success
 */
#ifdef FPGA_TEST_9
#define MAX_CPU_WRITES 0
#define MAX_CPU_READS 0
#define MAX_WR_REQ 2
#define MAX_RD_REQ 1
void two_writes_one_read_same_channel_with_response();
#endif


/*
 * Based on Example 1 (top of page), page 43 - with fence
 *
 * WrReq(x, 1, mdata1) = 1
 * WrFence(1, mdata)
 * WrReq(x, 1 ,mdata2) = 2
 *
 * RdReq(x, 1, mdata)
 * r1 = RdRsp(mdata)
 *
 *
 * !(r1 == 1)
 *
 * Success
 */
#ifdef FPGA_TEST_10
#define MAX_CPU_WRITES 0
#define MAX_CPU_READS 0
#define MAX_WR_REQ 3
#define MAX_RD_REQ 1
void two_writes_one_read_same_channel_with_fence();
#endif


/*
 * Suggested by example 4, page 43 (top of page)
 *

 * RdReq(x, VA, mdata)
 *
 * WrReq(x, VA, mdata) = 1
 *
 * r1 = RdRsp( mdata)
 *
 *
 * !(r1 == 0)
 * Fail
 */
#ifdef FPGA_TEST_11
#define MAX_CPU_WRITES 0
#define MAX_CPU_READS 0
#define MAX_WR_REQ 1
#define MAX_RD_REQ 1
void one_read_one_write_any_channel_no_sync();
#endif


#endif /* tests_FPGA_H_ */
