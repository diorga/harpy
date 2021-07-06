#include "tests_fpga.h"

unsigned char nondet_uchar();
extern unsigned char sharedMemory[MAX_LOC];

extern WrBuffer wrBuffer1;
extern WrBuffer wrBuffer2;

extern ReqPool wrReqPool;
extern ReqPool rdReqPool;

extern Channel upstreamChannels[MAX_CHANNELS];
extern Channel downstreamChannels[MAX_CHANNELS];

#ifdef FPGA_TEST_1
void one_write_one_read_any_channel_with_response() {

  unsigned char i0, i1, i2, i3;

  i0 = nondet_uchar();
  i1 = nondet_uchar();
  i2 = nondet_uchar();
  i3 = nondet_uchar();

  __CPROVER_assume(i0 < i1);
  __CPROVER_assume(i1 < i2);
  __CPROVER_assume(i2 < i3);
  __CPROVER_assume(i3 < MAX_TIME);

  __CPROVER_assume (
      (g_history[i0].type == WrReq) &&
      (g_history[i0].address == 0) &&
      (g_history[i0].data == 1) &&
      (g_history[i0].mdata == 0) &&

      (g_history[i1].type == WrRsp) &&
      (g_history[i1].mdata == 0) &&

      (g_history[i2].type == RdReq) &&
      (g_history[i2].address == 0) &&
      (g_history[i2].mdata == 0) &&

      (g_history[i3].type == RdRsp) &&
      (g_history[i3].mdata == 0) &&

      (wrReq_issued == 1) &&
      (rdReq_issued == 1) &&
      (cpuWrites_issued == 0) &&
      (cpuReads_issued == 0)
    );
    __CPROVER_assume(wrBuffer1.num_pending_operations == 0);
    __CPROVER_assume(wrBuffer2.num_pending_operations == 0);
    __CPROVER_assume(wrReqPool.num_pending_operations == 0);
    __CPROVER_assume(rdReqPool.num_pending_operations == 0);
    __CPROVER_assume(upstreamChannels[0].num_pending_operations == 0);
    __CPROVER_assume(upstreamChannels[1].num_pending_operations == 0);
    __CPROVER_assume(downstreamChannels[0].num_pending_operations == 0);
    __CPROVER_assume(downstreamChannels[1].num_pending_operations == 0);
  int r1 = g_history[i3].data;
  __CPROVER_assert(
                          !(r1 == 0),
                          "One write, one read -- any channel, with response \n \
                           Expected Fail"
                        );

}
#endif

#ifdef FPGA_TEST_2
void one_write_one_read_same_channel_with_response() {

  unsigned char i0, i1, i2, i3;

  i0 = nondet_uchar();
  i1 = nondet_uchar();
  i2 = nondet_uchar();
  i3 = nondet_uchar();

  __CPROVER_assume(i0 < i1);
  __CPROVER_assume(i1 < i2);
  __CPROVER_assume(i2 < i3);
  __CPROVER_assume(i3 < MAX_TIME);

  __CPROVER_assume (
      (g_history[i0].type == WrReq) &&
      (g_history[i0].address == 0) &&
      (g_history[i0].data == 1) &&
      (g_history[i0].mdata == 0) &&
      (g_history[i0].channel == 0) &&

      (g_history[i1].type == WrRsp) &&
      (g_history[i1].mdata == 0) &&

      (g_history[i2].type == RdReq) &&
      (g_history[i2].address == 0) &&
      (g_history[i2].mdata == 0) &&
      (g_history[i2].channel == 0) &&

      (g_history[i3].type == RdRsp) &&
      (g_history[i3].mdata == 0) &&

      (wrReq_issued == 1) &&
      (rdReq_issued == 1) &&
      (cpuWrites_issued == 0) &&
      (cpuReads_issued == 0)
    );
    __CPROVER_assume(wrBuffer1.num_pending_operations == 0);
    __CPROVER_assume(wrBuffer2.num_pending_operations == 0);
    __CPROVER_assume(wrReqPool.num_pending_operations == 0);
    __CPROVER_assume(rdReqPool.num_pending_operations == 0);
    __CPROVER_assume(upstreamChannels[0].num_pending_operations == 0);
    __CPROVER_assume(upstreamChannels[1].num_pending_operations == 0);
    __CPROVER_assume(downstreamChannels[0].num_pending_operations == 0);
    __CPROVER_assume(downstreamChannels[1].num_pending_operations == 0);
    int r1 = g_history[i3].data;
    __CPROVER_assert(
                          !(r1 == 0),
                          "One write, one read -- same channel, with response \n \
                           Expected Success"
                       );
}
#endif

#ifdef FPGA_TEST_3
void one_write_one_read_any_channel_with_fence() {

  unsigned char i0, i1, i2, i3, i4, i5, i6, i7;

  i0 = nondet_uchar();
  i1 = nondet_uchar();
  i2 = nondet_uchar();
  i3 = nondet_uchar();
  i4 = nondet_uchar();
  i5 = nondet_uchar();
  i6 = nondet_uchar();
  i7 = nondet_uchar();

  __CPROVER_assume(i0 < i1);
  __CPROVER_assume(i1 < i2);
  __CPROVER_assume(i2 < i3);
  __CPROVER_assume(i3 < i4);
  __CPROVER_assume(i4 < i5);
  __CPROVER_assume(i5 < i6);
  __CPROVER_assume(i6 < i7);
  __CPROVER_assume(i7 < MAX_TIME);

  __CPROVER_assume (
      (g_history[i0].type == WrReq) &&
      (g_history[i0].address == 0) &&
      (g_history[i0].data == 1) &&
      (g_history[i0].mdata == 1) &&

      (g_history[i1].type == WrRsp) &&
      (g_history[i1].mdata == 1) &&

      (g_history[i2].type == FnReq) &&
      (g_history[i2].channel == VA) &&
      (g_history[i2].mdata == 80) &&

      (g_history[i3].type == FnRsp) &&
      (g_history[i3].mdata == 80) &&

      (g_history[i4].type == RdReq) &&
      (g_history[i4].address == 0) &&
      (g_history[i4].mdata == 30) &&

      (g_history[i5].type == RdRsp) &&
      (g_history[i5].mdata == 30) &&

      (wrReq_issued == 2) &&
      (rdReq_issued == 1) &&
      (cpuWrites_issued == 0) &&
      (cpuReads_issued == 0)
    );
    __CPROVER_assume(wrBuffer1.num_pending_operations == 0);
    __CPROVER_assume(wrBuffer2.num_pending_operations == 0);
    __CPROVER_assume(wrReqPool.num_pending_operations == 0);
    __CPROVER_assume(rdReqPool.num_pending_operations == 0);
    __CPROVER_assume(upstreamChannels[0].num_pending_operations == 0);
    __CPROVER_assume(upstreamChannels[1].num_pending_operations == 0);
    __CPROVER_assume(downstreamChannels[0].num_pending_operations == 0);
    __CPROVER_assume(downstreamChannels[1].num_pending_operations == 0);
    int r1 = g_history[i5].data;
    __CPROVER_assert(
                        !(r1 == 0),
                        "One write, one read -- same channel, with fence \n \
                         Expected Success"
                      );
}
#endif


#ifdef FPGA_TEST_4
void two_writes_two_reads_same_channel_with_response() {

  unsigned char i0, i1, i2, i3, i4, i5, i6, i7;

  i0 = nondet_uchar();
  i1 = nondet_uchar();
  i2 = nondet_uchar();
  i3 = nondet_uchar();
  i4 = nondet_uchar();
  i5 = nondet_uchar();
  i6 = nondet_uchar();
  i7 = nondet_uchar();

  __CPROVER_assume(i0 < i1);
  __CPROVER_assume(i1 < i2);
  __CPROVER_assume(i2 < i3);
  __CPROVER_assume(i3 < i4);
  __CPROVER_assume(i4 < i5);
  __CPROVER_assume(i5 < i6);
  __CPROVER_assume(i6 < i7);
  __CPROVER_assume(i7 < MAX_TIME);

  __CPROVER_assume (
      (g_history[i0].type == WrReq) &&
      (g_history[i0].address == 0) &&
      (g_history[i0].data == 1) &&
      (g_history[i0].mdata == 0) &&
      (g_history[i0].channel == 0) &&

      (g_history[i1].type == WrRsp) &&
      (g_history[i1].mdata == 0) &&

      (g_history[i2].type == WrReq) &&
      (g_history[i2].address == 0) &&
      (g_history[i2].data == 2) &&
      (g_history[i2].mdata == 1) &&
      (g_history[i2].channel == 0) &&

      (g_history[i3].type == WrRsp) &&
      (g_history[i3].mdata == 1) &&

      (g_history[i4].type == RdReq) &&
      (g_history[i4].address == 0) &&
      (g_history[i4].mdata == 0) &&
      (g_history[i4].channel == 0) &&

      (g_history[i5].type == RdRsp) &&
      (g_history[i5].mdata == 0) &&

      (g_history[i6].type == RdReq) &&
      (g_history[i6].address == 0) &&
      (g_history[i6].mdata == 1) &&
      (g_history[i6].channel == 0) &&

      (g_history[i7].type == RdRsp) &&
      (g_history[i7].mdata == 1) &&

      (wrReq_issued == 2) &&
      (rdReq_issued == 2) &&
      (cpuWrites_issued == 0) &&
      (cpuReads_issued == 0)
    );
    __CPROVER_assume(wrBuffer1.num_pending_operations == 0);
    __CPROVER_assume(wrBuffer2.num_pending_operations == 0);
    __CPROVER_assume(wrReqPool.num_pending_operations == 0);
    __CPROVER_assume(rdReqPool.num_pending_operations == 0);
    __CPROVER_assume(upstreamChannels[0].num_pending_operations == 0);
    __CPROVER_assume(upstreamChannels[1].num_pending_operations == 0);
    __CPROVER_assume(downstreamChannels[0].num_pending_operations == 0);
    __CPROVER_assume(downstreamChannels[1].num_pending_operations == 0);
       int r1 = g_history[i5].data;
       int r2 = g_history[i7].data;
       __CPROVER_assert(
                        !((r1 == 2) && (r2 == 1)),
                        "Two writes, two reads -- same channel, with response \n \
                         Expected Success"
                       );
}
#endif


#ifdef FPGA_TEST_5
void two_writes_two_reads_any_channel_with_response() {

  unsigned char i0, i1, i2, i3, i4, i5, i6, i7;

  i0 = nondet_uchar();
  i1 = nondet_uchar();
  i2 = nondet_uchar();
  i3 = nondet_uchar();
  i4 = nondet_uchar();
  i5 = nondet_uchar();
  i6 = nondet_uchar();
  i7 = nondet_uchar();

  __CPROVER_assume(i0 < i1);
  __CPROVER_assume(i1 < i2);
  __CPROVER_assume(i2 < i3);
  __CPROVER_assume(i3 < i4);
  __CPROVER_assume(i4 < i5);
  __CPROVER_assume(i5 < i6);
  __CPROVER_assume(i6 < i7);
  __CPROVER_assume(i7 < MAX_TIME);

  __CPROVER_assume ((g_history[i0].type == WrReq) &&
      (g_history[i0].address == 0) &&
      (g_history[i0].data == 1) &&
      (g_history[i0].mdata == 0) &&

      (g_history[i1].type == WrRsp) &&
      (g_history[i1].mdata == 0) &&

      (g_history[i2].type == WrReq) &&
      (g_history[i2].address == 0) &&
      (g_history[i2].data == 2) &&
      (g_history[i2].mdata == 1) &&

      (g_history[i3].type == WrRsp) &&
      (g_history[i3].mdata == 1) &&

      (g_history[i4].type == RdReq) &&
      (g_history[i4].address == 0) &&
      (g_history[i4].mdata == 0) &&

      (g_history[i5].type == RdRsp) &&
      (g_history[i5].mdata == 0) &&

      (g_history[i6].type == RdReq) &&
      (g_history[i6].address == 0) &&
      (g_history[i6].mdata == 1) &&

      (g_history[i7].type == RdRsp) &&
      (g_history[i7].mdata == 1) &&

      (wrReq_issued == 2) &&
      (rdReq_issued == 2) &&
      (cpuWrites_issued == 0) &&
      (cpuReads_issued == 0)
    );
    __CPROVER_assume(wrBuffer1.num_pending_operations == 0);
    __CPROVER_assume(wrBuffer2.num_pending_operations == 0);
    __CPROVER_assume(wrReqPool.num_pending_operations == 0);
    __CPROVER_assume(rdReqPool.num_pending_operations == 0);
    __CPROVER_assume(upstreamChannels[0].num_pending_operations == 0);
    __CPROVER_assume(upstreamChannels[1].num_pending_operations == 0);
    __CPROVER_assume(downstreamChannels[0].num_pending_operations == 0);
    __CPROVER_assume(downstreamChannels[1].num_pending_operations == 0);
    int r1 = g_history[i5].data;
    int r2 = g_history[i7].data;
    __CPROVER_assert(
                        !((r1 == 2) && (r2 == 1)),
                        "Two writes, two reads -- same channel, with response \n \
                         Expected Fail"
                       );
}
#endif


#ifdef FPGA_TEST_6
void two_writes_two_reads_different_channel_no_sync() {

  unsigned char i0,i1,i2,i3,i4,i5;

  i0 = nondet_uchar();
  i1 = nondet_uchar();
  i2 = nondet_uchar();
  i3 = nondet_uchar();
  i4 = nondet_uchar();
  i5 = nondet_uchar();

  __CPROVER_assume(i0 < i1);
  __CPROVER_assume(i1 < i2);
  __CPROVER_assume(i2 < i3);
  __CPROVER_assume(i3 < i4);
  __CPROVER_assume(i4 < i5);
  __CPROVER_assume(i5 < MAX_TIME);


  __CPROVER_assume (
      (g_history[i0].type == WrReq) &&
      (g_history[i0].address == 0) &&
      (g_history[i0].data == 1) &&
      (g_history[i0].mdata == 0) &&
      (g_history[i0].channel == 0) &&

      (g_history[i1].type == WrReq) &&
      (g_history[i1].address == 0) &&
      (g_history[i1].data == 2) &&
      (g_history[i1].mdata == 1) &&
      (g_history[i1].channel == 1) &&

      (g_history[i2].type == RdReq) &&
      (g_history[i2].address == 0) &&
      (g_history[i2].mdata == 0) &&

      (g_history[i3].type == RdRsp) &&
      (g_history[i3].mdata == 0) &&

      (g_history[i4].type == RdReq) &&
      (g_history[i4].address == 0) &&
      (g_history[i4].mdata == 1) &&

      (g_history[i5].type == RdRsp) &&
      (g_history[i5].mdata == 1) &&

      (wrReq_issued == 2) &&
      (rdReq_issued == 2) &&
      (cpuWrites_issued == 0) &&
      (cpuReads_issued == 0)
    );
    __CPROVER_assume(wrBuffer1.num_pending_operations == 0);
    __CPROVER_assume(wrBuffer2.num_pending_operations == 0);
    __CPROVER_assume(wrReqPool.num_pending_operations == 0);
    __CPROVER_assume(rdReqPool.num_pending_operations == 0);
    __CPROVER_assume(upstreamChannels[0].num_pending_operations == 0);
    __CPROVER_assume(upstreamChannels[1].num_pending_operations == 0);
    __CPROVER_assume(downstreamChannels[0].num_pending_operations == 0);
    __CPROVER_assume(downstreamChannels[1].num_pending_operations == 0);
    int r1 = g_history[i3].data;
    int r2 = g_history[i5].data;
    __CPROVER_assert(
                        !((r1 == 2) && (r2 == 1)),
                        "Two writes, two reads -- different channel, no sync \n \
                         Expected Fail"
                       );
}
#endif


#ifdef FPGA_TEST_7
void two_writes_two_reads_any_channel_with_fence() {

  unsigned char i0, i1, i2, i3, i4, i5, i6;

  i0 = nondet_uchar();
  i1 = nondet_uchar();
  i2 = nondet_uchar();
  i3 = nondet_uchar();
  i4 = nondet_uchar();
  i5 = nondet_uchar();
  i6 = nondet_uchar();

  __CPROVER_assume(i0 < i1);
  __CPROVER_assume(i1 < i2);
  __CPROVER_assume(i2 < i3);
  __CPROVER_assume(i3 < i4);
  __CPROVER_assume(i4 < i5);
  __CPROVER_assume(i5 < i6);
  __CPROVER_assume(i6 < MAX_TIME);

  __CPROVER_assume (
      (g_history[i0].type == WrReq) &&
      (g_history[i0].address == 0) &&
      (g_history[i0].data == 1) &&
      (g_history[i0].mdata == 0) &&

      (g_history[i1].type == FnReq) &&
      (g_history[i1].channel == VA) &&
      (g_history[i1].mdata == 1) &&

      (g_history[i2].type == WrReq) &&
      (g_history[i2].address == 0) &&
      (g_history[i2].data == 2) &&
      (g_history[i2].mdata == 2) &&

      (g_history[i3].type == RdReq) &&
      (g_history[i3].address == 0) &&
      (g_history[i3].mdata == 0) &&

      (g_history[i4].type == RdRsp) &&
      (g_history[i4].mdata == 0) &&

      (g_history[i5].type == RdReq) &&
      (g_history[i5].address == 0) &&
      (g_history[i5].mdata == 1) &&

      (g_history[i6].type == RdRsp) &&
      (g_history[i6].mdata == 1) &&

      (wrReq_issued == 3) &&
      (rdReq_issued == 2) &&
      (cpuWrites_issued == 0) &&
      (cpuReads_issued == 0)
    );
    __CPROVER_assume(wrBuffer1.num_pending_operations == 0);
    __CPROVER_assume(wrBuffer2.num_pending_operations == 0);
    __CPROVER_assume(wrReqPool.num_pending_operations == 0);
    __CPROVER_assume(rdReqPool.num_pending_operations == 0);
    __CPROVER_assume(upstreamChannels[0].num_pending_operations == 0);
    __CPROVER_assume(upstreamChannels[1].num_pending_operations == 0);
    __CPROVER_assume(downstreamChannels[0].num_pending_operations == 0);
    __CPROVER_assume(downstreamChannels[1].num_pending_operations == 0);
    int r1 = g_history[i4].data;
    int r2 = g_history[i6].data;
    __CPROVER_assert(
                        !((r1 == 2) && (r2 == 1)),
                        "Two writes, two reads -- different channel, with fence \n \
                         Expected Success"
                       );
}
#endif


#ifdef FPGA_TEST_8
void two_writes_one_read_same_channel_no_sync() {

  unsigned char i0, i1, i2, i3;

  i0 = nondet_uchar();
  i1 = nondet_uchar();
  i2 = nondet_uchar();
  i3 = nondet_uchar();

  __CPROVER_assume(i0 < i1);
  __CPROVER_assume(i1 < i2);
  __CPROVER_assume(i2 < i3);
  __CPROVER_assume(i3 < MAX_TIME);

  __CPROVER_assume (
      (g_history[i0].type == WrReq) &&
      (g_history[i0].address == 0) &&
      (g_history[i0].data == 1) &&
      (g_history[i0].mdata == 0) &&
      (g_history[i0].channel == 1) &&

      (g_history[i1].type == WrReq) &&
      (g_history[i1].address == 0) &&
      (g_history[i1].data == 2) &&
      (g_history[i1].mdata == 1) &&
      (g_history[i1].channel == 1) &&

      (g_history[i2].type == RdReq) &&
      (g_history[i2].address == 0) &&
      (g_history[i2].mdata == 0) &&
      (g_history[i2].channel == 1) &&

      (g_history[i3].type == RdRsp) &&
      (g_history[i3].mdata == 0) &&

      (wrReq_issued == 2) &&
      (rdReq_issued == 1) &&
      (cpuWrites_issued == 0) &&
      (cpuReads_issued == 0)
    );
    __CPROVER_assume(wrBuffer1.num_pending_operations == 0);
    __CPROVER_assume(wrBuffer2.num_pending_operations == 0);
    __CPROVER_assume(wrReqPool.num_pending_operations == 0);
    __CPROVER_assume(rdReqPool.num_pending_operations == 0);
    __CPROVER_assume(upstreamChannels[0].num_pending_operations == 0);
    __CPROVER_assume(upstreamChannels[1].num_pending_operations == 0);
    __CPROVER_assume(downstreamChannels[0].num_pending_operations == 0);
    __CPROVER_assume(downstreamChannels[1].num_pending_operations == 0);
    int r1 = g_history[i3].data;
    __CPROVER_assert(
                          !(r1 == 1),
                          "Two writes, one read -- same channel, no sync\n \
                           Expected Fail"
                       );
}
#endif

#ifdef FPGA_TEST_9
void two_writes_one_read_same_channel_with_response() {

  unsigned char i0, i1, i2, i3, i4, i5;

  i0 = nondet_uchar();
  i1 = nondet_uchar();
  i2 = nondet_uchar();
  i3 = nondet_uchar();
  i4 = nondet_uchar();
  i5 = nondet_uchar();

  __CPROVER_assume(i0 < i1);
  __CPROVER_assume(i1 < i2);
  __CPROVER_assume(i2 < i3);
  __CPROVER_assume(i3 < i4);
  __CPROVER_assume(i4 < i5);
  __CPROVER_assume(i5 < MAX_TIME);

  __CPROVER_assume (
      (g_history[i0].type == WrReq) &&
      (g_history[i0].address == 0) &&
      (g_history[i0].data == 1) &&
      (g_history[i0].mdata == 0) &&
      (g_history[i0].channel == 1) &&

      (g_history[i1].type == WrRsp) &&
      (g_history[i1].mdata == 0) &&

      (g_history[i2].type == WrReq) &&
      (g_history[i2].address == 0) &&
      (g_history[i2].data == 2) &&
      (g_history[i2].mdata == 1) &&
      (g_history[i2].channel == 1) &&

      (g_history[i3].type == WrRsp) &&
      (g_history[i3].mdata == 1) &&

      (g_history[i4].type == RdReq) &&
      (g_history[i4].address == 0) &&
      (g_history[i4].mdata == 0) &&
      (g_history[i4].channel == 1) &&

      (g_history[i5].type == RdRsp) &&
      (g_history[i5].mdata == 0) &&

      (wrReq_issued == 2) &&
      (rdReq_issued == 1) &&
      (cpuWrites_issued == 0) &&
      (cpuReads_issued == 0)
    );
    __CPROVER_assume(wrBuffer1.num_pending_operations == 0);
    __CPROVER_assume(wrBuffer2.num_pending_operations == 0);
    __CPROVER_assume(wrReqPool.num_pending_operations == 0);
    __CPROVER_assume(rdReqPool.num_pending_operations == 0);
    __CPROVER_assume(upstreamChannels[0].num_pending_operations == 0);
    __CPROVER_assume(upstreamChannels[1].num_pending_operations == 0);
    __CPROVER_assume(downstreamChannels[0].num_pending_operations == 0);
    __CPROVER_assume(downstreamChannels[1].num_pending_operations == 0);
    int r1 = g_history[i5].data;
    __CPROVER_assert(
                          (r1 == 2),
                          "Two writes, one read -- same channel, write response \n \
                           Expected Success"
                       );

}
#endif

#ifdef FPGA_TEST_10
void two_writes_one_read_same_channel_with_fence() {

  unsigned char i0, i1, i2, i3, i4;

  i0 = nondet_uchar();
  i1 = nondet_uchar();
  i2 = nondet_uchar();
  i3 = nondet_uchar();
  i4 = nondet_uchar();

  __CPROVER_assume(i0 < i1);
  __CPROVER_assume(i1 < i2);
  __CPROVER_assume(i2 < i3);
  __CPROVER_assume(i3 < i4);
  __CPROVER_assume(i4 < MAX_TIME);

  __CPROVER_assume (
      (g_history[i0].type == WrReq) &&
      (g_history[i0].address == 0) &&
      (g_history[i0].data == 1) &&
      (g_history[i0].mdata == 0) &&
      (g_history[i0].channel == 1) &&

      (g_history[i1].type == FnReq) &&
      (g_history[i1].channel == 1) &&

      (g_history[i2].type == WrReq) &&
      (g_history[i2].address == 0) &&
      (g_history[i2].data == 2) &&
      (g_history[i2].mdata == 1) &&
      (g_history[i2].channel == 1) &&

      (g_history[i3].type == RdReq) &&
      (g_history[i3].address == 0) &&
      (g_history[i3].mdata == 0) &&
      (g_history[i3].channel == 1) &&

      (g_history[i4].type == RdRsp) &&
      (g_history[i4].mdata == 0) &&

      (wrReq_issued == 3) &&
      (rdReq_issued == 1) &&
      (cpuWrites_issued == 0) &&
      (cpuReads_issued == 0)
    );
    __CPROVER_assume(wrBuffer1.num_pending_operations == 0);
    __CPROVER_assume(wrBuffer2.num_pending_operations == 0);
    __CPROVER_assume(wrReqPool.num_pending_operations == 0);
    __CPROVER_assume(rdReqPool.num_pending_operations == 0);
    __CPROVER_assume(upstreamChannels[0].num_pending_operations == 0);
    __CPROVER_assume(upstreamChannels[1].num_pending_operations == 0);
    __CPROVER_assume(downstreamChannels[0].num_pending_operations == 0);
    __CPROVER_assume(downstreamChannels[1].num_pending_operations == 0);
    int r1 = g_history[i4].data;
    __CPROVER_assert(
                          !(sharedMemory[0] == 1),
                          "Two writes, one read -- same channel, with fence \n \
                           Expected Success"
                       );


}
#endif

#ifdef FPGA_TEST_11
void one_read_one_write_any_channel_no_sync() {

  unsigned char i0, i1, i2, i3, i4;

  i0 = nondet_uchar();
  i1 = nondet_uchar();
  i2 = nondet_uchar();

  __CPROVER_assume(i0 < i1);
  __CPROVER_assume(i1 < i2);
  __CPROVER_assume(i2 < MAX_TIME);

  __CPROVER_assume (
      (g_history[i0].type == RdReq) &&
      (g_history[i0].address == 0) &&
      (g_history[i0].mdata == 0) &&

      (g_history[i1].type == WrReq) &&
      (g_history[i1].address == 0) &&
      (g_history[i1].data == 1) &&
      (g_history[i1].mdata == 0) &&

      (g_history[i2].type == RdRsp) &&
      (g_history[i2].mdata == 0) &&

      (wrReq_issued == 1) &&
      (rdReq_issued == 1) &&
      (cpuWrites_issued == 0) &&
      (cpuReads_issued == 0)
    );
    __CPROVER_assume(wrBuffer1.num_pending_operations == 0);
    __CPROVER_assume(wrBuffer2.num_pending_operations == 0);
    __CPROVER_assume(wrReqPool.num_pending_operations == 0);
    __CPROVER_assume(rdReqPool.num_pending_operations == 0);
    __CPROVER_assume(upstreamChannels[0].num_pending_operations == 0);
    __CPROVER_assume(upstreamChannels[1].num_pending_operations == 0);
    __CPROVER_assume(downstreamChannels[0].num_pending_operations == 0);
    __CPROVER_assume(downstreamChannels[1].num_pending_operations == 0);
    int r1 = g_history[i2].data;
    __CPROVER_assert(
                          (r1 == 0),
                          "One read, one write -- any channel, no sync \n \
                           Expected Fail"
                       );

}
#endif
