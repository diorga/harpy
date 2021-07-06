CC = goto-cc
UNWIND = 30 --unwinding-assertions
TRACE =

all: harp_all
.PHONY : verify_all
verify_all: verify_fpga verify_cpu_fpga verify_queue

.PHONY : harp_all
harp_all: harp_fpga harp_cpu_fpga harp_queue

.PHONY : verify_alloy
verify_alloy: alloy_traces
	cbmc alloy_traces --unwind $(UNWIND) $(TRACE)
	echo  Done verifying alloy traces

.PHONY : verify_fpga
verify_fpga: 		verify_fpga_1 verify_fpga_2 verify_fpga_3 verify_fpga_4 \
					verify_fpga_5 verify_fpga_6 verify_fpga_7 verify_fpga_8 \
					verify_fpga_9 verify_fpga_10 verify_fpga_11
	echo  Done verifying FPGA-only litmus tests

.PHONY : verify_cpu_fpga
verify_cpu_fpga: 	verify_cpu_fpga_1 verify_cpu_fpga_2 verify_cpu_fpga_3 \
   					verify_cpu_fpga_4 verify_cpu_fpga_5 verify_cpu_fpga_6
	echo  Done verifying FPGA-CPU litmus tests

.PHONY : verify_queue
verify_queue: 		verify_queue_1 verify_queue_2 verify_queue_3 verify_queue_4 \
					verify_queue_5 verify_queue_6 verify_queue_7 verify_queue_8
	echo  Done verifying QUEUE litmus tests

verify_queue_part1: verify_queue_1 verify_queue_2 verify_queue_3 verify_queue_4
	echo  Done verifying QUEUE litmus testsi part1

verify_queue_part2: verify_queue_5 verify_queue_6 verify_queue_7 verify_queue_8
	echo  Done verifying QUEUE litmus tests part2

.PHONY : harp_fpga
harp_fpga: 			harp_fpga_1 harp_fpga_2 harp_fpga_3 harp_fpga_4 \
					harp_fpga_5 harp_fpga_6 harp_fpga_7 harp_fpga_8 \
					harp_fpga_9 harp_fpga_10 harp_fpga_11
	echo  Done compiling FPGA-only litmus tests

.PHONY : harp_cpu_fpga
harp_cpu_fpga: 		harp_cpu_fpga_1 harp_cpu_fpga_2 harp_cpu_fpga_3 \
   					harp_cpu_fpga_4 harp_cpu_fpga_5 harp_cpu_fpga_6
	echo  Done compiling FPGA-CPU litmus tests

.PHONY : harp_queue
harp_queue: 		harp_queue_1 harp_queue_2 harp_queue_3 harp_queue_4 \
					harp_queue_5 harp_queue_6 harp_queue_7 harp_queue_8
	echo  Done compiling QUEUE litmus tests


.PHONY : verify_fpga_1
verify_fpga_1: harp_fpga_1
	cbmc harp_fpga_1  --unwind $(UNWIND) $(TRACE)
.PHONY : verify_fpga_2
verify_fpga_2: harp_fpga_2
	cbmc harp_fpga_2  --unwind $(UNWIND) $(TRACE)
.PHONY : verify_fpga_3
verify_fpga_3: harp_fpga_3
	cbmc harp_fpga_3  --unwind $(UNWIND) $(TRACE)
.PHONY : verify_fpga_4
verify_fpga_4: harp_fpga_4
	cbmc harp_fpga_4  --unwind $(UNWIND) $(TRACE)
.PHONY : verify_fpga_5
verify_fpga_5: harp_fpga_5BAME
	cbmc harp_fpga_5  --unwind $(UNWIND) $(TRACE)
.PHONY : verify_fpga_6
verify_fpga_6: harp_fpga_6
	cbmc harp_fpga_6  --unwind $(UNWIND) $(TRACE)
.PHONY : verify_fpga_7
verify_fpga_7: harp_fpga_7
	cbmc harp_fpga_7  --unwind $(UNWIND) $(TRACE)
.PHONY : verify_fpga_8
verify_fpga_8: harp_fpga_8
	cbmc harp_fpga_8  --unwind $(UNWIND) $(TRACE)
.PHONY : verify_fpga_9
verify_fpga_9: harp_fpga_9
	cbmc harp_fpga_9  --unwind $(UNWIND) $(TRACE)
.PHONY : verify_fpga_10
verify_fpga_10: harp_fpga_10
	cbmc harp_fpga_10 --unwind $(UNWIND) $(TRACE)
.PHONY : verify_fpga_11
verify_fpga_11: harp_fpga_11
	cbmc harp_fpga_11 --unwind $(UNWIND) $(TRACE)

.PHONY : verify_cpu_fpga_1
verify_cpu_fpga_1: harp_cpu_fpga_1
	cbmc harp_cpu_fpga_1 --unwind $(UNWIND) $(TRACE)
.PHONY : verify_cpu_fpga_2
verify_cpu_fpga_2: harp_cpu_fpga_2
	cbmc harp_cpu_fpga_2 --unwind $(UNWIND) $(TRACE)
.PHONY : verify_cpu_fpga_3
verify_cpu_fpga_3: harp_cpu_fpga_3
	cbmc harp_cpu_fpga_3 --unwind $(UNWIND) $(TRACE)
.PHONY : verify_cpu_fpga_4
verify_cpu_fpga_4: harp_cpu_fpga_4
	cbmc harp_cpu_fpga_4 --unwind $(UNWIND) $(TRACE)
.PHONY : verify_cpu_fpga_5
verify_cpu_fpga_5: harp_cpu_fpga_5
	cbmc harp_cpu_fpga_5 --unwind $(UNWIND) $(TRACE)
.PHONY : verify_cpu_fpga_6
verify_cpu_fpga_6: harp_cpu_fpga_6
	cbmc harp_cpu_fpga_6 --unwind $(UNWIND) $(TRACE)

.PHONY : verify_queue_1
verify_queue_1: harp_queue_1
	cbmc harp_queue_1 --unwind $(UNWIND) $(TRACE)
.PHONY : verify_queue_2
verify_queue_2: harp_queue_2
	cbmc harp_queue_2 --unwind $(UNWIND) $(TRACE)
.PHONY : verify_queue_3
verify_queue_3: harp_queue_3
	cbmc harp_queue_3 --unwind $(UNWIND) $(TRACE)
.PHONY : verify_queue_4
verify_queue_4: harp_queue_4
	cbmc harp_queue_4 --unwind $(UNWIND) $(TRACE)
.PHONY : verify_queue_5
verify_queue_5: harp_queue_5
	cbmc harp_queue_5 --unwind $(UNWIND) $(TRACE)
.PHONY : verify_queue_6
verify_queue_6: harp_queue_6
	cbmc harp_queue_6 --unwind $(UNWIND) $(TRACE)
.PHONY : verify_queue_7
verify_queue_7: harp_queue_7
	cbmc harp_queue_7 --unwind $(UNWIND) $(TRACE)
.PHONY : verify_queue_8
verify_queue_8: harp_queue_8
	cbmc harp_queue_8 --unwind $(UNWIND) $(TRACE)

.PHONY : verify_multiple_threads_1
verify_multiple_threads_1: harp_multiple_threads_1
	cbmc harp_multiple_threads_1 --unwind $(UNWIND) $(TRACE)
.PHONY : verify_multiple_threads_2
verify_store_buffering: harp_multiple_threads_2
	cbmc harp_multiple_threads_2 --unwind $(UNWIND) $(TRACE)
verify_store_buffering_fence: harp_multiple_threads_3
	cbmc harp_multiple_threads_3 --unwind $(UNWIND) $(TRACE)

harp_fpga_1: actors.o
	$(CC) -DTESTS_FPGA -DFPGA_TEST_1  actors.o tests_fpga.c harp.c -o harp_fpga_1
harp_fpga_2: actors.o
	$(CC) -DTESTS_FPGA -DFPGA_TEST_2  actors.o tests_fpga.c harp.c -o harp_fpga_2
harp_fpga_3: actors.o
	$(CC) -DTESTS_FPGA -DFPGA_TEST_3  actors.o tests_fpga.c harp.c -o harp_fpga_3
harp_fpga_4: actors.o
	$(CC) -DTESTS_FPGA -DFPGA_TEST_4  actors.o tests_fpga.c harp.c -o harp_fpga_4
harp_fpga_5: actors.o
	$(CC) -DTESTS_FPGA -DFPGA_TEST_5  actors.o tests_fpga.c harp.c -o harp_fpga_5
harp_fpga_6: actors.o
	$(CC) -DTESTS_FPGA -DFPGA_TEST_6  actors.o tests_fpga.c harp.c -o harp_fpga_6
harp_fpga_7: actors.o
	$(CC) -DTESTS_FPGA -DFPGA_TEST_7  actors.o tests_fpga.c harp.c -o harp_fpga_7
harp_fpga_8: actors.o
	$(CC) -DTESTS_FPGA -DFPGA_TEST_8  actors.o tests_fpga.c harp.c -o harp_fpga_8
harp_fpga_9: actors.o
	$(CC) -DTESTS_FPGA -DFPGA_TEST_9  actors.o tests_fpga.c harp.c -o harp_fpga_9
harp_fpga_10: actors.o
	$(CC) -DTESTS_FPGA -DFPGA_TEST_10 actors.o tests_fpga.c harp.c -o harp_fpga_10
harp_fpga_11: actors.o
	$(CC) -DTESTS_FPGA -DFPGA_TEST_11 actors.o tests_fpga.c harp.c -o harp_fpga_11

harp_cpu_fpga_1: actors.o
	$(CC) -DTESTS_CPU_FPGA -DFPGA_CPU_TEST_1 actors.o tests_cpu_fpga.c harp.c -o harp_cpu_fpga_1
harp_cpu_fpga_2: actors.o
	$(CC) -DTESTS_CPU_FPGA -DFPGA_CPU_TEST_2 actors.o tests_cpu_fpga.c harp.c -o harp_cpu_fpga_2
harp_cpu_fpga_3: actors.o
	$(CC) -DTESTS_CPU_FPGA -DFPGA_CPU_TEST_3 actors.o tests_cpu_fpga.c harp.c -o harp_cpu_fpga_3
harp_cpu_fpga_4: actors.o
	$(CC) -DTESTS_CPU_FPGA -DFPGA_CPU_TEST_4 actors.o tests_cpu_fpga.c harp.c -o harp_cpu_fpga_4
harp_cpu_fpga_5: actors.o
	$(CC) -DTESTS_CPU_FPGA -DFPGA_CPU_TEST_5 actors.o tests_cpu_fpga.c harp.c -o harp_cpu_fpga_5
harp_cpu_fpga_6: actors.o
	$(CC) -DTESTS_CPU_FPGA -DFPGA_CPU_TEST_6 actors.o tests_cpu_fpga.c harp.c -o harp_cpu_fpga_6

harp_queue_1: actors.o
	$(CC) -DTESTS_QUEUE -DQUEUE_TEST_1 actors.o tests_queue.c harp.c -o harp_queue_1
harp_queue_2: actors.o
	$(CC) -DTESTS_QUEUE -DQUEUE_TEST_2 actors.o tests_queue.c harp.c -o harp_queue_2
harp_queue_3: actors.o
	$(CC) -DTESTS_QUEUE -DQUEUE_TEST_3 actors.o tests_queue.c harp.c -o harp_queue_3
harp_queue_4: actors.o
	$(CC) -DTESTS_QUEUE -DQUEUE_TEST_4 actors.o tests_queue.c harp.c -o harp_queue_4
harp_queue_5: actors.o
	$(CC) -DTESTS_QUEUE -DQUEUE_TEST_5 actors.o tests_queue.c harp.c -o harp_queue_5
harp_queue_6: actors.o
	$(CC) -DTESTS_QUEUE -DQUEUE_TEST_6 actors.o tests_queue.c harp.c -o harp_queue_6
harp_queue_7: actors.o
	$(CC) -DTESTS_QUEUE -DQUEUE_TEST_7 actors.o tests_queue.c harp.c -o harp_queue_7
harp_queue_8: actors.o
	$(CC) -DTESTS_QUEUE -DQUEUE_TEST_8 actors.o tests_queue.c harp.c -o harp_queue_8

harp_multiple_threads_1: actors.o
	$(CC) -DTESTS_MULTIPLE_THREADS -DJOHN_EXAMPLE actors.o tests_multiple_threads.c harp.c -o harp_multiple_threads_1
harp_multiple_threads_2: actors.o
	$(CC) -DTESTS_MULTIPLE_THREADS -DSTORE_BUFFERING actors.o tests_multiple_threads.c harp.c -o harp_multiple_threads_2
harp_multiple_threads_3: actors.o
	$(CC) -DTESTS_MULTIPLE_THREADS -DSTORE_BUFFERING_FENCE actors.o tests_multiple_threads.c harp.c -o harp_multiple_threads_3

alloy_traces: actors.o
	$(CC) -DALLOY_TRACES -DTRACE_0 actors.o alloy_traces.c harp.c -o alloy_traces

actors.o: actors.c actors.h

%.o: %.c
	$(CC) -c $<

clean:
	rm -rf alloy_traces harp_queue* harp_cpu_fpga* harp_fpga* harp_multiple_threads* harp *.o



.PHONY: all clean
