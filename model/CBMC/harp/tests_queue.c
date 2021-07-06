
#include "tests_queue.h"

unsigned char nondet_uchar();


extern unsigned char sharedMemory[MAX_LOC];


#ifdef QUEUE_TEST_1
void queue_no_mpf_single_channel_FPGA_enqueue_FPGA_enqueue() {

  unsigned char fpga_i0, fpga_i1, fpga_i2, fpga_i3;
  unsigned char fpga_i4, fpga_i5, fpga_i6, fpga_i7;
  unsigned char fpga_i8, fpga_i9;

  unsigned char tail = 0;
  unsigned char head = 0;


  fpga_i0  = nondet_uchar();
  fpga_i1  = nondet_uchar();
  fpga_i2  = nondet_uchar();
  fpga_i3  = nondet_uchar();

  fpga_i4  = nondet_uchar();
  fpga_i5  = nondet_uchar();
  fpga_i6  = nondet_uchar();
  fpga_i7  = nondet_uchar();

  fpga_i8  = nondet_uchar();
  fpga_i9  = nondet_uchar();

  __CPROVER_assume(fpga_i0  < fpga_i1);
  __CPROVER_assume(fpga_i1  < fpga_i2);
  __CPROVER_assume(fpga_i2  < fpga_i3);
  __CPROVER_assume(fpga_i3  < fpga_i4);
  __CPROVER_assume(fpga_i4  < fpga_i5);
  __CPROVER_assume(fpga_i5  < fpga_i6);
  __CPROVER_assume(fpga_i6  < fpga_i7);
  __CPROVER_assume(fpga_i7  < fpga_i8);
  __CPROVER_assume(fpga_i8  < fpga_i9);
  __CPROVER_assume(fpga_i9 < MAX_TIME);


  __CPROVER_assume(

      (g_history[fpga_i0].type == WrReq) &&
      (g_history[fpga_i0].address == QUEUE_ADDR + tail) &&
      (g_history[fpga_i0].data == 42) &&
      (g_history[fpga_i0].mdata == 0) &&
      (g_history[fpga_i0].channel == 0) &&

      (g_history[fpga_i1].type == WrRsp) &&
      (g_history[fpga_i1].mdata == 0) &&

      (g_history[fpga_i2].type == WrReq) &&
      (g_history[fpga_i2].address == TAIL_ADDR) &&
      (g_history[fpga_i2].data == (tail + 1) % QUEUE_SIZE ) &&
      (g_history[fpga_i2].mdata == 1) &&
      (g_history[fpga_i2].channel == 0) &&

      (g_history[fpga_i3].type == WrRsp) &&
      (g_history[fpga_i3].mdata == 1) &&


      (g_history[fpga_i4].type == WrReq) &&
      (g_history[fpga_i4].address == QUEUE_ADDR + ((tail + 1) % QUEUE_SIZE) ) &&
      (g_history[fpga_i4].data == 43) &&
      (g_history[fpga_i4].mdata == 2) &&
      (g_history[fpga_i4].channel == 0) &&

      (g_history[fpga_i5].type == WrRsp) &&
      (g_history[fpga_i5].mdata == 2) &&

      (g_history[fpga_i6].type == WrReq) &&
      (g_history[fpga_i6].address == TAIL_ADDR) &&
      (g_history[fpga_i6].data == (tail + 2) % QUEUE_SIZE ) &&
      (g_history[fpga_i6].mdata == 3) &&
      (g_history[fpga_i6].channel == 0) &&

      (g_history[fpga_i7].type == WrRsp) &&
      (g_history[fpga_i7].mdata == 3) &&


      (g_history[fpga_i8].type == FnReq) &&
      (g_history[fpga_i8].channel == 0) &&
      (g_history[fpga_i8].mdata == 4) &&

      (g_history[fpga_i9].type == FnRsp) &&
      (g_history[fpga_i9].mdata == 4) &&

      (wrReq_issued == 5) &&
      (rdReq_issued == 0) &&
      (cpuWrites_issued == 0) &&
      (cpuReads_issued == 0)
    );
//    __CPROVER_assert(0, "Dead 1");
    __CPROVER_assert( (sharedMemory[QUEUE_ADDR] == 42) && (sharedMemory[QUEUE_ADDR+1] == 43) &&
                      (sharedMemory[TAIL_ADDR] == 2),
                      "Queue no mpf single channel enque after enqueue ");

}
#endif

#ifdef QUEUE_TEST_2
void queue_no_mpf_single_channel_FPGA_dequeue_FPGA_dequeue() {

  unsigned char fpga_i0, fpga_i1, fpga_i2, fpga_i3;
  unsigned char fpga_i4, fpga_i5, fpga_i6, fpga_i7;
  unsigned char fpga_i8, fpga_i9;
  unsigned char head = 0;
  unsigned char tail = 2;

  fpga_i0  = nondet_uchar();
  fpga_i1  = nondet_uchar();
  fpga_i2  = nondet_uchar();
  fpga_i3  = nondet_uchar();

  fpga_i4  = nondet_uchar();
  fpga_i5  = nondet_uchar();
  fpga_i6  = nondet_uchar();
  fpga_i7  = nondet_uchar();

  fpga_i8  = nondet_uchar();
  fpga_i9  = nondet_uchar();

  __CPROVER_assume(fpga_i0 < fpga_i1);
  __CPROVER_assume(fpga_i1 < fpga_i2);
  __CPROVER_assume(fpga_i2 < fpga_i3);
  __CPROVER_assume(fpga_i3 < fpga_i4);
  __CPROVER_assume(fpga_i4 < fpga_i5);
  __CPROVER_assume(fpga_i5 < fpga_i6);
  __CPROVER_assume(fpga_i6 < fpga_i7);
  __CPROVER_assume(fpga_i7 < fpga_i8);
  __CPROVER_assume(fpga_i8 < fpga_i9);
  __CPROVER_assume(fpga_i9 < MAX_TIME);


  __CPROVER_assume(
      (g_history[fpga_i0].type == RdReq) &&
      (g_history[fpga_i0].address == QUEUE_ADDR + head) &&
      (g_history[fpga_i0].mdata == 0) &&
      (g_history[fpga_i0].channel == 0) &&

      (g_history[fpga_i1].type == RdRsp) &&
      (g_history[fpga_i1].mdata == 0) &&

      (g_history[fpga_i2].type == WrReq) &&
      (g_history[fpga_i2].address == HEAD_ADDR) &&
      (g_history[fpga_i2].data == (head + 1) % QUEUE_SIZE ) &&
      (g_history[fpga_i2].mdata == 0) &&
      (g_history[fpga_i2].channel == 0) &&

      (g_history[fpga_i3].type == WrRsp) &&
      (g_history[fpga_i3].mdata == 0) &&


      (g_history[fpga_i4].type == RdReq) &&
      (g_history[fpga_i4].address == QUEUE_ADDR + (head + 1) % QUEUE_SIZE ) &&
      (g_history[fpga_i4].mdata == 1) &&
      (g_history[fpga_i4].channel == 0) &&

      (g_history[fpga_i5].type == RdRsp) &&
      (g_history[fpga_i5].mdata == 1) &&

      (g_history[fpga_i6].type == WrReq) &&
      (g_history[fpga_i6].address == HEAD_ADDR) &&
      (g_history[fpga_i6].data == (head + 2) % QUEUE_SIZE ) &&
      (g_history[fpga_i6].mdata == 1) &&
      (g_history[fpga_i6].channel == 0) &&

      (g_history[fpga_i7].type == WrRsp) &&
      (g_history[fpga_i7].mdata == 1) &&


      (g_history[fpga_i8].type == FnReq) &&
      (g_history[fpga_i8].channel == 0) &&
      (g_history[fpga_i8].mdata == 2) &&

      (g_history[fpga_i9].type == FnRsp) &&
      (g_history[fpga_i9].mdata == 2) &&

      (wrReq_issued == 3) &&
      (rdReq_issued == 2) &&
      (cpuWrites_issued == 0) &&
      (cpuReads_issued == 0)
    );
//  __CPROVER_assert(0, "Dead 2");
  __CPROVER_assert( (g_history[fpga_i1].data == 42) && (g_history[fpga_i5].data == 43) &&
                    (sharedMemory[HEAD_ADDR] == 2),
                    "Queue no mpf single channel denque after denqueue \n \
                     Expected Success"
                  );

}
#endif

#ifdef QUEUE_TEST_3
void queue_no_mpf_single_channel_FPGA_enqueue_CPU_dequeue() {

  unsigned char fpga_i0, fpga_i1, fpga_i2, fpga_i3;
  unsigned char cpu_i0, cpu_i1, cpu_i2;
  unsigned char tail = 0;
  unsigned char head = 0;

  fpga_i0 = nondet_uchar();
  fpga_i1 = nondet_uchar();
  fpga_i2 = nondet_uchar();
  fpga_i3 = nondet_uchar();

  cpu_i0  = nondet_uchar();
  cpu_i1  = nondet_uchar();
  cpu_i2  = nondet_uchar();

  __CPROVER_assume(fpga_i0 < fpga_i1);
  __CPROVER_assume(fpga_i1 < fpga_i2);
  __CPROVER_assume(fpga_i2 < fpga_i3);
  //__CPROVER_assume(fpga_i3 < cpu_i0);
  __CPROVER_assume(fpga_i3 < MAX_TIME);

  __CPROVER_assume(cpu_i0 < cpu_i1);
  __CPROVER_assume(cpu_i1 < cpu_i2);
  __CPROVER_assume(cpu_i2 < MAX_TIME);


  __CPROVER_assume(

      (g_history[fpga_i0].type == WrReq) &&
      (g_history[fpga_i0].address == QUEUE_ADDR + tail) &&
      (g_history[fpga_i0].mdata == 0) &&
      (g_history[fpga_i0].channel == 0) &&
      (g_history[fpga_i0].data == 42) &&

      (g_history[fpga_i1].type == WrRsp) &&
      (g_history[fpga_i1].mdata == 0) &&

      (g_history[fpga_i2].type == WrReq) &&
      (g_history[fpga_i2].address == TAIL_ADDR) &&
      (g_history[fpga_i2].data == (tail + 1) % QUEUE_SIZE ) &&
      (g_history[fpga_i2].mdata == 1) &&
      (g_history[fpga_i2].channel == 0) &&

      (g_history[fpga_i3].type == WrRsp) &&
      (g_history[fpga_i3].mdata == 1) &&


      (g_history[cpu_i0].type == CpuRead) &&
      (g_history[cpu_i0].address == TAIL_ADDR) &&

      (g_history[cpu_i0].data != head) &&

      (g_history[cpu_i1].type == CpuRead) &&
      (g_history[cpu_i1].address == QUEUE_ADDR + head) &&

      (g_history[cpu_i2].type == CpuWrite) &&
      (g_history[cpu_i2].address == HEAD_ADDR) &&
      (g_history[cpu_i2].data == (head + 1) % QUEUE_SIZE) &&

      (wrReq_issued == 2) &&
      (rdReq_issued == 0) &&
      (cpuWrites_issued == 1) &&
      (cpuReads_issued == 2)
   );
//    __CPROVER_assert(0, "Dead 3");
    __CPROVER_assert( (g_history[cpu_i1].data == 42) && (sharedMemory[TAIL_ADDR] == 1),
                    "Queue no mpf single channel FPGA enque then CPU dequeue \n \
                     Expected Success"
                   );
}
#endif

#ifdef QUEUE_TEST_4
void queue_no_mpf_single_channel_CPU_enqueue_FPGA_dequeue() {

  unsigned char cpu_i0, cpu_i1;
  unsigned char fpga_i0, fpga_i1, fpga_i2, fpga_i3, fpga_i4, fpga_i5;
  unsigned char tail = 0;
  unsigned char head = 0;

  cpu_i0  = nondet_uchar();
  cpu_i1  = nondet_uchar();

  fpga_i0 = nondet_uchar();
  fpga_i1 = nondet_uchar();
  fpga_i2 = nondet_uchar();
  fpga_i3 = nondet_uchar();
  fpga_i4 = nondet_uchar();
  fpga_i5 = nondet_uchar();


  __CPROVER_assume(cpu_i0 < cpu_i1);
//  __CPROVER_assume(cpu_i1 < fpga_i0);
  __CPROVER_assume(cpu_i1 < MAX_TIME);

  __CPROVER_assume(fpga_i0 < fpga_i1);
  __CPROVER_assume(fpga_i1 < fpga_i2);
  __CPROVER_assume(fpga_i2 < fpga_i3);
  __CPROVER_assume(fpga_i3 < fpga_i4);
  __CPROVER_assume(fpga_i4 < fpga_i5);
  __CPROVER_assume(fpga_i5 < MAX_TIME);


  __CPROVER_assume(
      (g_history[cpu_i0].type == CpuWrite) &&
      (g_history[cpu_i0].address == QUEUE_ADDR + tail) &&
      (g_history[cpu_i0].data == 42) &&

      (g_history[cpu_i1].type == CpuWrite) &&
      (g_history[cpu_i1].address == TAIL_ADDR) &&
      (g_history[cpu_i1].data == (tail + 1) % QUEUE_SIZE) &&

      (g_history[fpga_i0].type == RdReq) &&
      (g_history[fpga_i0].address == TAIL_ADDR) &&
      (g_history[fpga_i0].mdata == 0) &&
      (g_history[fpga_i0].channel == 0) &&

      (g_history[fpga_i1].type == RdRsp) &&
      (g_history[fpga_i1].mdata == 0) &&

      (g_history[fpga_i1].data != head) &&

      (g_history[fpga_i2].type == RdReq) &&
      (g_history[fpga_i2].address == QUEUE_ADDR + head) &&
      (g_history[fpga_i2].mdata == 1) &&
      (g_history[fpga_i2].channel == 0) &&

      (g_history[fpga_i3].type == RdRsp) &&
      (g_history[fpga_i3].mdata == 1) &&

      (g_history[fpga_i4].type == WrReq) &&
      (g_history[fpga_i4].address == HEAD_ADDR) &&
      (g_history[fpga_i4].data == (head + 1) % QUEUE_SIZE ) &&
      (g_history[fpga_i4].mdata == 0) &&
      (g_history[fpga_i4].channel == 0) &&

      (g_history[fpga_i5].type == WrRsp) &&
      (g_history[fpga_i5].mdata == 0) &&

      (wrReq_issued == 1) &&
      (rdReq_issued == 2) &&
      (cpuWrites_issued == 2) &&
      (cpuReads_issued == 0)
    );
//    __CPROVER_assert(0, "Dead 4");
    __CPROVER_assert( (g_history[fpga_i3].data == 42) && (sharedMemory[TAIL_ADDR] == 1),
                      "Queue no mpf single channel FPGA enque then CPU dequeue \n \
                      Expected Success"
                    );
}
#endif

#ifdef QUEUE_TEST_5
void queue_no_mpf_multiple_channels_FPGA_enqueue_FPGA_enqueue() {

  unsigned char fpga_i0, fpga_i1, fpga_i2, fpga_i3;
  unsigned char fpga_i4, fpga_i5, fpga_i6, fpga_i7;
  unsigned char tail = 0;
  unsigned char head = 0;

  fpga_i0  = nondet_uchar();
  fpga_i1  = nondet_uchar();
  fpga_i2  = nondet_uchar();
  fpga_i3  = nondet_uchar();
  fpga_i4  = nondet_uchar();
  fpga_i5  = nondet_uchar();
  fpga_i6  = nondet_uchar();
  fpga_i7  = nondet_uchar();


  __CPROVER_assume(fpga_i0 < fpga_i1);
  __CPROVER_assume(fpga_i1 < fpga_i2);
  __CPROVER_assume(fpga_i2 < fpga_i3);
  __CPROVER_assume(fpga_i3 < fpga_i4);
  __CPROVER_assume(fpga_i4 < fpga_i5);
  __CPROVER_assume(fpga_i5 < fpga_i6);
  __CPROVER_assume(fpga_i6 < fpga_i7);
  __CPROVER_assume(fpga_i7 < MAX_TIME);


  __CPROVER_assume(
      (g_history[fpga_i0].type == WrReq) &&
      (g_history[fpga_i0].address == QUEUE_ADDR + tail) &&
      (g_history[fpga_i0].data == 42) &&
      (g_history[fpga_i0].mdata == 0) &&
      (g_history[fpga_i0].channel == VA) &&

      (g_history[fpga_i1].type == FnReq) &&
      (g_history[fpga_i1].channel == VA) &&
      (g_history[fpga_i1].mdata == 1) &&

      (g_history[fpga_i2].type == WrReq) &&
      (g_history[fpga_i2].address == HEAD_ADDR) &&
      (g_history[fpga_i2].data == (tail + 1) % QUEUE_SIZE ) &&
      (g_history[fpga_i2].mdata == 2) &&
      (g_history[fpga_i2].channel == VA) &&


      (g_history[fpga_i3].type == WrReq) &&
      (g_history[fpga_i3].address == QUEUE_ADDR + (tail + 1) % QUEUE_SIZE) &&
      (g_history[fpga_i3].data == 43) &&
      (g_history[fpga_i3].mdata == 3) &&
      (g_history[fpga_i3].channel == VA) &&

      (g_history[fpga_i4].type == FnReq) &&
      (g_history[fpga_i4].channel == VA) &&
      (g_history[fpga_i4].mdata == 4) &&

      (g_history[fpga_i5].type == WrReq) &&
      (g_history[fpga_i5].address == TAIL_ADDR) &&
      (g_history[fpga_i5].data == (tail + 2) % QUEUE_SIZE ) &&
      (g_history[fpga_i5].mdata == 5) &&
      (g_history[fpga_i5].channel == VA) &&


      (g_history[fpga_i6].type == FnReq) &&
      (g_history[fpga_i6].channel == VA) &&
      (g_history[fpga_i6].mdata == 6) &&

      (g_history[fpga_i7].type == FnRsp) &&
      (g_history[fpga_i7].mdata == 6) &&

      (wrReq_issued == 7) &&
      (rdReq_issued == 0) &&
      (cpuWrites_issued == 0) &&
      (cpuReads_issued == 0)
    );
//    __CPROVER_assert(0, "Dead 5");
    __CPROVER_assert( (sharedMemory[QUEUE_ADDR] == 42) && (sharedMemory[QUEUE_ADDR+1] == 43) &&
                      (sharedMemory[TAIL_ADDR] == 2),
                      "Queue no mpf multiple channels enque after enqueue \n \
                       Expected Success"
                    );
}
#endif

#ifdef QUEUE_TEST_6
void queue_no_mpf_multiple_channels_FPGA_dequeue_FPGA_dequeue() {
  unsigned char fpga_i0, fpga_i1, fpga_i2, fpga_i3;
  unsigned char fpga_i4, fpga_i5, fpga_i6, fpga_i7;
  unsigned char fpga_i8, fpga_i9;
  unsigned char head = 0;
  unsigned char tail = 2;

  fpga_i0  = nondet_uchar();
  fpga_i1  = nondet_uchar();
  fpga_i2  = nondet_uchar();
  fpga_i3  = nondet_uchar();

  fpga_i4  = nondet_uchar();
  fpga_i5  = nondet_uchar();
  fpga_i6  = nondet_uchar();
  fpga_i7  = nondet_uchar();

  fpga_i8  = nondet_uchar();
  fpga_i9  = nondet_uchar();

  __CPROVER_assume(fpga_i0 < fpga_i1);
  __CPROVER_assume(fpga_i1 < fpga_i2);
  __CPROVER_assume(fpga_i2 < fpga_i3);
  __CPROVER_assume(fpga_i3 < fpga_i4);
  __CPROVER_assume(fpga_i4 < fpga_i5);
  __CPROVER_assume(fpga_i5 < fpga_i6);
  __CPROVER_assume(fpga_i6 < fpga_i7);
  __CPROVER_assume(fpga_i7 < fpga_i8);
  __CPROVER_assume(fpga_i8 < fpga_i9);
  __CPROVER_assume(fpga_i9 < MAX_TIME);


  __CPROVER_assume(
      (g_history[fpga_i0].type == RdReq) &&
      (g_history[fpga_i0].address == QUEUE_ADDR + head) &&
      (g_history[fpga_i0].mdata == 0) &&
      (g_history[fpga_i0].channel == VA) &&

      (g_history[fpga_i1].type == RdRsp) &&
      (g_history[fpga_i1].mdata == 0) &&

      (g_history[fpga_i2].type == WrReq) &&
      (g_history[fpga_i2].address == HEAD_ADDR) &&
      (g_history[fpga_i2].data == (head + 1) % QUEUE_SIZE ) &&
      (g_history[fpga_i2].mdata == 0) &&
      (g_history[fpga_i2].channel == VA) &&

      (g_history[fpga_i3].type == WrRsp) &&
      (g_history[fpga_i3].mdata == 0) &&


      (g_history[fpga_i4].type == RdReq) &&
      (g_history[fpga_i4].address == QUEUE_ADDR + (head + 1) % QUEUE_SIZE ) &&
      (g_history[fpga_i4].mdata == 1) &&
      (g_history[fpga_i4].channel == VA) &&

      (g_history[fpga_i5].type == RdRsp) &&
      (g_history[fpga_i5].mdata == 1) &&

      (g_history[fpga_i6].type == WrReq) &&
      (g_history[fpga_i6].address == HEAD_ADDR) &&
      (g_history[fpga_i6].data == (head + 2) % QUEUE_SIZE ) &&
      (g_history[fpga_i6].mdata == 1) &&
      (g_history[fpga_i6].channel == VA) &&

      (g_history[fpga_i7].type == WrRsp) &&
      (g_history[fpga_i7].mdata == 1) &&


      (g_history[fpga_i8].type == FnReq) &&
      (g_history[fpga_i8].channel == VA) &&
      (g_history[fpga_i8].mdata == 2) &&

      (g_history[fpga_i9].type == FnRsp) &&
      (g_history[fpga_i9].mdata == 2) &&

      (wrReq_issued == 3) &&
      (rdReq_issued == 2) &&
      (cpuWrites_issued == 0) &&
      (cpuReads_issued == 0)
    );
//    __CPROVER_assert(0, "Dead 6");
    __CPROVER_assert(
                      ((g_history[fpga_i1].data == 42) && (g_history[fpga_i5].data == 43)),
                       "Queue no mpf single channel denque after denqueue \n \
                       Expected Success"
                    );


}
#endif

#ifdef QUEUE_TEST_7
void queue_no_mpf_multiple_channels_FPGA_enqueue_CPU_dequeue() {

  unsigned char fpga_i0, fpga_i1, fpga_i2;
  unsigned char cpu_i0, cpu_i1, cpu_i2, cpu_i3;
  unsigned char tail = 0;
  unsigned char head = 0;

  fpga_i0 = nondet_uchar();
  fpga_i1 = nondet_uchar();
  fpga_i2 = nondet_uchar();

  cpu_i0 = nondet_uchar();
  cpu_i1 = nondet_uchar();
  cpu_i2 = nondet_uchar();

  __CPROVER_assume(fpga_i0 < fpga_i1);
  __CPROVER_assume(fpga_i1 < fpga_i2);
 // __CPROVER_assume(fpga_i2 < cpu_i0);
  __CPROVER_assume(fpga_i2 < MAX_TIME);

  __CPROVER_assume(cpu_i0 < cpu_i1);
  __CPROVER_assume(cpu_i1 < cpu_i2);
  __CPROVER_assume(cpu_i2 < cpu_i3);
  __CPROVER_assume(cpu_i3 < MAX_TIME);


  __CPROVER_assume(
      (g_history[fpga_i0].type == WrReq) &&
      (g_history[fpga_i0].address == QUEUE_ADDR + tail) &&
      (g_history[fpga_i0].data == 42) &&
      (g_history[fpga_i0].mdata == 0) &&
      (g_history[fpga_i0].channel == VA) &&

      (g_history[fpga_i1].type == FnReq) &&
      (g_history[fpga_i1].channel == VA) &&
      (g_history[fpga_i1].mdata == 1) &&

      (g_history[fpga_i2].type == WrReq) &&
      (g_history[fpga_i2].address == TAIL_ADDR) &&
      (g_history[fpga_i2].data == (tail + 1) % QUEUE_SIZE ) &&
      (g_history[fpga_i2].mdata == 2) &&
      (g_history[fpga_i2].channel == VA) &&

      (g_history[cpu_i0].type == CpuRead) &&
      (g_history[cpu_i0].address == TAIL_ADDR) &&

      (g_history[cpu_i0].data != head) &&

      (g_history[cpu_i1].type == CpuRead) &&
      (g_history[cpu_i1].address == QUEUE_ADDR + head) &&

      (g_history[cpu_i2].type == CpuWrite) &&
      (g_history[cpu_i2].address == HEAD_ADDR) &&
      (g_history[cpu_i2].data == (head + 1) % QUEUE_SIZE) &&

      (wrReq_issued == 3) &&
      (rdReq_issued == 0) &&
      (cpuWrites_issued == 1) &&
      (cpuReads_issued == 2)
      );
//    __CPROVER_assert(0, "Dead 7");
    __CPROVER_assert( (g_history[cpu_i1].data == 42) && (sharedMemory[TAIL_ADDR] == 1),
                      "Queue no mpf multiple channels FPGA enque then CPU dequeue \n \
                      Expected Success"
                    );
}
#endif

#ifdef QUEUE_TEST_8
void queue_no_mpf_multiple_channels_CPU_enqueue_FPGA_dequeue() {
  unsigned char cpu_i0, cpu_i1;
  unsigned char fpga_i0, fpga_i1, fpga_i2, fpga_i3, fpga_i4, fpga_i5;
  unsigned char tail = 0;
  unsigned char head = 0;

  cpu_i0  = nondet_uchar();
  cpu_i1  = nondet_uchar();

  fpga_i0 = nondet_uchar();
  fpga_i1 = nondet_uchar();
  fpga_i2 = nondet_uchar();
  fpga_i3 = nondet_uchar();
  fpga_i4 = nondet_uchar();
  fpga_i5 = nondet_uchar();


  __CPROVER_assume(cpu_i0 < cpu_i1);
//  __CPROVER_assume(cpu_i1 < fpga_i0);
  __CPROVER_assume(cpu_i1 < MAX_TIME);

  __CPROVER_assume(fpga_i0 < fpga_i1);
  __CPROVER_assume(fpga_i1 < fpga_i2);
  __CPROVER_assume(fpga_i2 < fpga_i3);
  __CPROVER_assume(fpga_i3 < fpga_i4);
  __CPROVER_assume(fpga_i4 < fpga_i5);
  __CPROVER_assume(fpga_i5 < MAX_TIME);


  __CPROVER_assume(
      (g_history[cpu_i0].type == CpuWrite) &&
      (g_history[cpu_i0].address == QUEUE_ADDR + tail) &&
      (g_history[cpu_i0].data == 42) &&

      (g_history[cpu_i1].type == CpuWrite) &&
      (g_history[cpu_i1].address == TAIL_ADDR) &&
      (g_history[cpu_i1].data == (tail + 1) % QUEUE_SIZE) &&

      (g_history[fpga_i0].type == RdReq) &&
      (g_history[fpga_i0].address == TAIL_ADDR) &&
      (g_history[fpga_i0].mdata == 0) &&
      (g_history[fpga_i0].channel == VA) &&

      (g_history[fpga_i1].type == RdRsp) &&
      (g_history[fpga_i1].mdata == 0) &&

      (g_history[fpga_i1].data != head) &&

      (g_history[fpga_i2].type == RdReq) &&
      (g_history[fpga_i2].address == QUEUE_ADDR + head) &&
      (g_history[fpga_i2].mdata == 1) &&
      (g_history[fpga_i2].channel == VA) &&

      (g_history[fpga_i3].type == RdRsp) &&
      (g_history[fpga_i3].mdata == 1) &&

      (g_history[fpga_i4].type == WrReq) &&
      (g_history[fpga_i4].address == HEAD_ADDR) &&
      (g_history[fpga_i4].data == (head + 1) % QUEUE_SIZE ) &&
      (g_history[fpga_i4].mdata == 0) &&
      (g_history[fpga_i4].channel == VA) &&

      (g_history[fpga_i5].type == WrRsp) &&
      (g_history[fpga_i5].mdata == 0) &&

      (wrReq_issued == 1) &&
      (rdReq_issued == 2) &&
      (cpuWrites_issued == 2) &&
      (cpuReads_issued == 0)
    );

//    __CPROVER_assert(0, "Dead 8");
    __CPROVER_assert( (g_history[fpga_i3].data == 42) && (sharedMemory[TAIL_ADDR] == 1),
                      "Queue no mpf multiple channels FPGA enque then CPU dequeue \n \
                       Expected Success"
                    );

}
#endif
