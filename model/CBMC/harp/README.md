### CBMC implementation of the X+F memory model
The model is used to verify the correctness of our semantics.

#### Running the verification
To check FPGA only. The traces are described in *tests_fpga.h*

```
make -j8 verify_fpga
```

To check CPU-FPGA. The traces are described in *tests_cpu_fpga.h*

```
make -j8 verify_cpu_fpga
```

To check queue. The traces are described in *tests_queue.h*
```
make -j8 verify_queue
```
