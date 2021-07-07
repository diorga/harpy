# The semantics of Shared Memory in Intel CPU/FPGA Systems artifact

The aim of this artifact is to demonstrate the claims made in the paper "The Semantics of Shared Memory in Intel CPU/FPGA Systems". Here we will provide the means by which the following statements will be verified:

1. **Claim 1**: Our operational model, implemented in CBMC is consisten with the traces provided in the Intel manual
2. **Claim 2**: Basic queue operations are validated against the operational model
3. 

## Setup

### Git
Clone the main git repo using the following command

```
git clone https://github.com/diorga/harpy.git
```
 
### Docker

From within the git git repo, build the docker image

```
docker build -t diorga/harpy -f artifact/Dockerfile .
```

Next, start the docker container

```
docker run -it diorga/harpy sh
```

This should start a docker containter where all the experiments can be run.

## Claim 1: Our operational model is consistent with the manual traces
The manual traces can be found in the following files:
1. [FPGA only traces](model/CBMC/harp/tests_fpga.h)
2. [CPU-FPGA traces](model/CBMC/harp/tests_cpu_fpga.h)

Each file presents the trace and points to the paragraph in the Intel manual where it is described. To verify all the traces against the operational model, run the following commands from the docker container:

```
    cd backend
    python3 backend.py --manual_traces
```
This will run all traces and described in the manual and print a message if the traces were reproducible or not:

There are two parameters that can be changed at this stage. The number of traces that will be verified concurently and the maximum unwind depth. To change the number of concurent verifications, specify the **cores** command line argument and to change the unwind depth, specify the **unwind** command line argument.

For example, the following command runs the same experiment but uses 8 cores instead of 4 and uses an unwind depth of 30.

```
    python3 backend.py --manual_traces --cores 8 --unwind 30
    
```

## Claim 2: The queue is validated against our operational model
We verify enqueue and dequeue operations against our CBMC implementation and the file that presents these operations can be found here:
[Queue tests](model/CBMC/harp/tests_queue.h)

```
    cd backend
    python3 backend.py --queue_traces
```
This verifies only behaviour that sho


