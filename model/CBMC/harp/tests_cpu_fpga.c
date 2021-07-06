#include "tests_cpu_fpga.h"
extern unsigned char sharedMemory[MAX_LOC];

extern WrBuffer wrBuffer1;
extern WrBuffer wrBuffer2;

extern ReqPool wrReqPool;
extern ReqPool rdReqPool;

extern Channel upstreamChannels[MAX_CHANNELS];
extern Channel downstreamChannels[MAX_CHANNELS];

unsigned char nondet_uchar();


#ifdef FPGA_CPU_TEST_1
void fpga_2writes_cpu_2reads_same_channel_with_response() {

  unsigned char fpga_i0, fpga_i1, fpga_i2, fpga_i3;
  unsigned char cpu_i0, cpu_i1;

  fpga_i0 = nondet_uchar();
  fpga_i1 = nondet_uchar();
  fpga_i2 = nondet_uchar();
  fpga_i3 = nondet_uchar();
  cpu_i0 = nondet_uchar();
  cpu_i1 = nondet_uchar();

  __CPROVER_assume(fpga_i0 < fpga_i1);
  __CPROVER_assume(fpga_i1 < fpga_i2);
  __CPROVER_assume(fpga_i2 < fpga_i3);
  __CPROVER_assume(fpga_i3 < MAX_TIME);

  __CPROVER_assume(cpu_i0 < cpu_i1);
  __CPROVER_assume(cpu_i1 < MAX_TIME);

  __CPROVER_assume (
      (g_history[fpga_i0].type == WrReq) &&
      (g_history[fpga_i0].address == 0) &&
      (g_history[fpga_i0].data == 1) &&
      (g_history[fpga_i0].mdata == 0) &&
      (g_history[fpga_i0].channel == 0) &&

      (g_history[fpga_i1].type == WrRsp) &&
      (g_history[fpga_i1].mdata == 0) &&

      (g_history[fpga_i2].type == WrReq) &&
      (g_history[fpga_i2].address == 0) &&
      (g_history[fpga_i2].data == 2) &&
      (g_history[fpga_i2].mdata == 1) &&
      (g_history[fpga_i2].channel == 0) &&

      (g_history[fpga_i3].type == WrRsp) &&
      (g_history[fpga_i3].mdata == 1) &&

      (g_history[cpu_i0].type == CpuRead) &&
      (g_history[cpu_i0].address == 0) &&

      (g_history[cpu_i1].type == CpuRead) &&
      (g_history[cpu_i1].address == 0) &&

      (wrReq_issued == 2) &&
      (rdReq_issued == 0) &&
      (cpuWrites_issued == 0) &&
      (cpuReads_issued == 2)
    );
    __CPROVER_assume(wrBuffer1.num_pending_operations == 0);
    __CPROVER_assume(wrBuffer2.num_pending_operations == 0);
    __CPROVER_assume(wrReqPool.num_pending_operations == 0);
    __CPROVER_assume(rdReqPool.num_pending_operations == 0);
    __CPROVER_assume(upstreamChannels[0].num_pending_operations == 0);
    __CPROVER_assume(upstreamChannels[1].num_pending_operations == 0);
    __CPROVER_assume(downstreamChannels[0].num_pending_operations == 0);
    __CPROVER_assume(downstreamChannels[1].num_pending_operations == 0);
       int r1 = g_history[cpu_i0].data;
       int r2 = g_history[cpu_i1].data;
       __CPROVER_assert(
                        !((r1 == 2) && (r2 == 1)),
                        "Two fpga writes, two cpu reads -- same channel, with response \n \
                         Expected Success"
                       );

}
#endif

#ifdef FPGA_CPU_TEST_2
void fpga_2writes_cpu_2reads_any_channel_with_response() {

  unsigned char fpga_i0, fpga_i1, fpga_i2, fpga_i3;
  unsigned char cpu_i0, cpu_i1;

  fpga_i0 = nondet_uchar();
  fpga_i1 = nondet_uchar();
  fpga_i2 = nondet_uchar();
  fpga_i3 = nondet_uchar();
  cpu_i0 = nondet_uchar();
  cpu_i1 = nondet_uchar();

  __CPROVER_assume(fpga_i0 < fpga_i1);
  __CPROVER_assume(fpga_i1 < fpga_i2);
  __CPROVER_assume(fpga_i2 < fpga_i3);
  __CPROVER_assume(fpga_i3 < MAX_TIME);

  __CPROVER_assume(cpu_i0 < cpu_i1);
  __CPROVER_assume(cpu_i1 < MAX_TIME);

  __CPROVER_assume (
      (g_history[fpga_i0].type == WrReq) &&
      (g_history[fpga_i0].address == 0) &&
      (g_history[fpga_i0].data == 1) &&
      (g_history[fpga_i0].mdata == 0) &&

      (g_history[fpga_i1].type == WrRsp) &&
      (g_history[fpga_i1].mdata == 0) &&

      (g_history[fpga_i2].type == WrReq) &&
      (g_history[fpga_i2].address == 0) &&
      (g_history[fpga_i2].data == 2) &&
      (g_history[fpga_i2].mdata == 1) &&

      (g_history[fpga_i3].type == WrRsp) &&
      (g_history[fpga_i3].mdata == 1) &&

      (g_history[cpu_i0].type == CpuRead) &&
      (g_history[cpu_i0].address == 0) &&

      (g_history[cpu_i1].type == CpuRead) &&
      (g_history[cpu_i1].address == 0) &&

      (wrReq_issued == 2) &&
      (rdReq_issued == 0) &&
      (cpuWrites_issued == 0) &&
      (cpuReads_issued == 2)
    );
    __CPROVER_assume(wrBuffer1.num_pending_operations == 0);
    __CPROVER_assume(wrBuffer2.num_pending_operations == 0);
    __CPROVER_assume(wrReqPool.num_pending_operations == 0);
    __CPROVER_assume(rdReqPool.num_pending_operations == 0);
    __CPROVER_assume(upstreamChannels[0].num_pending_operations == 0);
    __CPROVER_assume(upstreamChannels[1].num_pending_operations == 0);
    __CPROVER_assume(downstreamChannels[0].num_pending_operations == 0);
    __CPROVER_assume(downstreamChannels[1].num_pending_operations == 0);
    int r1 = g_history[cpu_i0].data;
    int r2 = g_history[cpu_i1].data;
    __CPROVER_assert(
                        !((r1 == 2) && (r2 == 1)),
                        "Two fpga writes, two fpga reads -- same channel, with response \n \
                         Expected Fail"
                       );
}
#endif


#ifdef FPGA_CPU_TEST_3
void fpga_2writes_cpu_2reads_different_channel_no_sync() {

  unsigned char fpga_i0, fpga_i1, fpga_i2, fpga_i3;
  unsigned char cpu_i0, cpu_i1;

  fpga_i0 = nondet_uchar();
  fpga_i1 = nondet_uchar();
  cpu_i0 = nondet_uchar();
  cpu_i1 = nondet_uchar();

  __CPROVER_assume(fpga_i0 < fpga_i1);
  __CPROVER_assume(fpga_i1 < MAX_TIME);

  __CPROVER_assume(cpu_i0 < cpu_i1);
  __CPROVER_assume(cpu_i1 < MAX_TIME);


  __CPROVER_assume (
      (g_history[fpga_i0].type == WrReq) &&
      (g_history[fpga_i0].address == 0) &&
      (g_history[fpga_i0].data == 1) &&
      (g_history[fpga_i0].mdata == 0) &&
      (g_history[fpga_i0].channel == 0) &&

      (g_history[fpga_i1].type == WrReq) &&
      (g_history[fpga_i1].address == 0) &&
      (g_history[fpga_i1].data == 2) &&
      (g_history[fpga_i1].mdata == 1) &&
      (g_history[fpga_i1].channel == 1) &&

      (g_history[cpu_i0].type == CpuRead) &&
      (g_history[cpu_i0].address == 0) &&

      (g_history[cpu_i1].type == CpuRead) &&
      (g_history[cpu_i1].address == 0) &&

      (wrReq_issued == 2) &&
      (rdReq_issued == 0) &&
      (cpuWrites_issued == 0) &&
      (cpuReads_issued == 2)

    );
    __CPROVER_assume(wrBuffer1.num_pending_operations == 0);
    __CPROVER_assume(wrBuffer2.num_pending_operations == 0);
    __CPROVER_assume(wrReqPool.num_pending_operations == 0);
    __CPROVER_assume(rdReqPool.num_pending_operations == 0);
    __CPROVER_assume(upstreamChannels[0].num_pending_operations == 0);
    __CPROVER_assume(upstreamChannels[1].num_pending_operations == 0);
    __CPROVER_assume(downstreamChannels[0].num_pending_operations == 0);
    __CPROVER_assume(downstreamChannels[1].num_pending_operations == 0);
    int r1 = g_history[cpu_i0].data;
    int r2 = g_history[cpu_i1].data;
     __CPROVER_assert(
                        !((r1 == 2) && (r2 == 1)),
                        "Two fpga writes, two cpu reads -- different channel, no sync \n \
                         Expected Fail"
                       );
}
#endif


#ifdef FPGA_CPU_TEST_4
void fpga_2writes_cpu_2reads_any_channel_with_fence() {

  unsigned char fpga_i0, fpga_i1, fpga_i2;
  unsigned char cpu_i0, cpu_i1;

  fpga_i0 = nondet_uchar();
  fpga_i1 = nondet_uchar();
  fpga_i2 = nondet_uchar();
  cpu_i0 = nondet_uchar();
  cpu_i1 = nondet_uchar();

  __CPROVER_assume(fpga_i0 < fpga_i1);
  __CPROVER_assume(fpga_i1 < fpga_i2);
  __CPROVER_assume(fpga_i2 < MAX_TIME);

  __CPROVER_assume(cpu_i0 < cpu_i1);
  __CPROVER_assume(cpu_i1 < MAX_TIME);

  __CPROVER_assume (
      (g_history[fpga_i0].type == WrReq) &&
      (g_history[fpga_i0].address == 0) &&
      (g_history[fpga_i0].data == 1) &&
      (g_history[fpga_i0].mdata == 0) &&

      (g_history[fpga_i1].type == FnReq) &&
      (g_history[fpga_i1].channel == VA) &&
      (g_history[fpga_i1].mdata == 1) &&

      (g_history[fpga_i2].type == WrReq) &&
      (g_history[fpga_i2].address == 0) &&
      (g_history[fpga_i2].data == 2) &&
      (g_history[fpga_i2].mdata == 2) &&

      (g_history[cpu_i0].type == CpuRead) &&
      (g_history[cpu_i0].address == 0) &&

      (g_history[cpu_i1].type == CpuRead) &&
      (g_history[cpu_i1].address == 0) &&

      (wrReq_issued == 3) &&
      (rdReq_issued == 0) &&
      (cpuWrites_issued == 0) &&
      (cpuReads_issued == 2)
    );
    __CPROVER_assume(wrBuffer1.num_pending_operations == 0);
    __CPROVER_assume(wrBuffer2.num_pending_operations == 0);
    __CPROVER_assume(wrReqPool.num_pending_operations == 0);
    __CPROVER_assume(rdReqPool.num_pending_operations == 0);
    __CPROVER_assume(upstreamChannels[0].num_pending_operations == 0);
    __CPROVER_assume(upstreamChannels[1].num_pending_operations == 0);
    __CPROVER_assume(downstreamChannels[0].num_pending_operations == 0);
    __CPROVER_assume(downstreamChannels[1].num_pending_operations == 0);
    int r1 = g_history[cpu_i0].data;
    int r2 = g_history[cpu_i1].data;
    __CPROVER_assert(
                        !((r1 == 2) && (r2 == 1)),
                        "Two fpga writes, two fpga reads -- different channel, with fence \n \
                         Expected Success"
                       );
}
#endif

#ifdef FPGA_CPU_TEST_5
void fpga_2reads_cpu_2writes_different_channel_no_sync() {

  unsigned char fpga_i0, fpga_i1, fpga_i2, fpga_i3;
  unsigned char cpu_i0, cpu_i1;

  fpga_i0 = nondet_uchar();
  fpga_i1 = nondet_uchar();
  fpga_i2 = nondet_uchar();
  fpga_i3 = nondet_uchar();
  cpu_i0 = nondet_uchar();
  cpu_i1 = nondet_uchar();

  __CPROVER_assume(fpga_i0 < fpga_i1);
  __CPROVER_assume(fpga_i1 < fpga_i2);
  __CPROVER_assume(fpga_i2 < fpga_i3);
  __CPROVER_assume(fpga_i3 < MAX_TIME);

  __CPROVER_assume(cpu_i0 < cpu_i1);
  __CPROVER_assume(cpu_i1 < MAX_TIME);

  __CPROVER_assume (
      (g_history[fpga_i0].type == RdReq) &&
      (g_history[fpga_i0].address == 0) &&
      (g_history[fpga_i0].channel == 0) &&

      (g_history[fpga_i1].type == RdReq) &&
      (g_history[fpga_i1].address == 0) &&
      (g_history[fpga_i1].channel == 1) &&

      (g_history[fpga_i2].type == RdRsp) &&

      (g_history[fpga_i3].type == RdRsp) &&

      (g_history[cpu_i0].type == CpuWrite) &&
      (g_history[cpu_i0].data == 1) &&
      (g_history[cpu_i0].address == 0) &&

      (g_history[cpu_i1].type == CpuWrite) &&
      (g_history[cpu_i1].data == 2) &&
      (g_history[cpu_i1].address == 0) &&

      (wrReq_issued == 0) &&
      (rdReq_issued == 2) &&
      (cpuWrites_issued == 2) &&
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
    int r1 = g_history[fpga_i2].data;
    int r2 = g_history[fpga_i3].data;
     __CPROVER_assert(
                        !((r1 == 2) && (r2 == 1)),
                        "Two fpga reads, two cpu writes -- different channel, no sync \n \
                         Expected Fail"
                       );


}
#endif

#ifdef FPGA_CPU_TEST_6
void fpga_2reads_cpu_2writes_same_channel_no_sync() {

  unsigned char fpga_i0, fpga_i1, fpga_i2, fpga_i3;
  unsigned char cpu_i0, cpu_i1;

  fpga_i0 = nondet_uchar();
  fpga_i1 = nondet_uchar();
  fpga_i2 = nondet_uchar();
  fpga_i3 = nondet_uchar();
  cpu_i0 = nondet_uchar();
  cpu_i1 = nondet_uchar();

  __CPROVER_assume(fpga_i0 < fpga_i1);
  __CPROVER_assume(fpga_i1 < fpga_i2);
  __CPROVER_assume(fpga_i2 < fpga_i3);
  __CPROVER_assume(fpga_i3 < MAX_TIME);

  __CPROVER_assume(cpu_i0 < cpu_i1);
  __CPROVER_assume(cpu_i1 < MAX_TIME);

  __CPROVER_assume (
      (g_history[fpga_i0].type == RdReq) &&
      (g_history[fpga_i0].address == 0) &&
      (g_history[fpga_i0].channel == 0) &&

      (g_history[fpga_i1].type == RdReq) &&
      (g_history[fpga_i1].address == 0) &&
      (g_history[fpga_i1].channel == 0) &&

      (g_history[fpga_i2].type == RdRsp) &&

      (g_history[fpga_i3].type == RdRsp) &&

      (g_history[cpu_i0].type == CpuWrite) &&
      (g_history[cpu_i0].data == 1) &&
      (g_history[cpu_i0].address == 0) &&

      (g_history[cpu_i1].type == CpuWrite) &&
      (g_history[cpu_i1].data == 2) &&
      (g_history[cpu_i1].address == 0) &&

      (wrReq_issued == 0) &&
      (rdReq_issued == 2) &&
      (cpuWrites_issued == 2) &&
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
    int r1 = g_history[fpga_i2].data;
    int r2 = g_history[fpga_i3].data;
     __CPROVER_assert(
                        !((r1 == 2) && (r2 == 1)),
                        "Two fpga reads, two cpu writes -- same channel, no sync \n \
                         Expected Success"
                       );

}
#endif
