# The semantics of Shared Memory in Intel CPU/FPGA Systems artifact

The aim of this artifact is to demonstrate the claims made in the paper "The Semantics of Shared Memory in Intel CPU/FPGA Systems". 

This manual is divided into two parts: **Getting Started Guide** that should be finished in 30 minutes and a section where we will provide the **Step by Step Instructions** by which the paper instructions can be reproduced.

## Getting Started Guide

### Git
Clone the main git repo using the following command

```
git clone https://github.com/diorga/harpy.git
```
 
### Docker

From within the git repo, build the docker image. 

```
docker build -t diorga/harpy -f artifact/Dockerfile .
```

Next, start the docker container

```
docker run -it diorga/harpy bash
```

This should start a docker container where all the experiments can be run.

#### Note

1. Depending on how you installed docker, you might need to prefix every docker command with **sudo**.
2. There is an alternative to building the docker image. You can direcly pull it from the docker repo using the following command
```
    docker pull diorga/harpy
```
3. The time it takes to build the docker container depends on the internet speed. Generally, it should take less than 10 minutes.
### Testing CBMC + Alloy
To verify that everything has been configured properly, run the following commands. 
```
    cd backend
    ./generate 4
    python3 backend.py --cbmc --run_cbmc --max_traces 2
```
This will use Alloy to generate all disallowed traces with 4 events. Afterwards, CBMC will verify just two of them. After this, a message that the traces could not be reproduced by the model will be displayed. 

#### Note

If the numbers of prallel threads is too big, the system can run out of memory and report the following message:
```
SAT checker ran out of memory
```
In this case, the system will not report the correct result.

### Hardware Setup

#### Create account
Our models are also validated on actual hardware. To gain access to the CPU/FPGA systems, an account is needed for the IL Academic Compute Environment. An account can be created by registering here:
https://registration.intel-research.net/register

This will require an intel lab sponsor. **Brent Forgeron** has agreed to help us for the review process. You should fill in his name in the 
**Intel Labs Sponsor for the Research Engagement** section. 

#### Connect to account

When the account is created, you should be able to connect to it using the following command:
```
ssh <username>@ssh-iam.intel-research.net            
source /export/fpga/bin/setup-fpga-env fpga-bdx-opae
```


## Step by Step Instructions

1. **Claim 1**: Our operational model, implemented in CBMC, is consistent with the traces provided in the Intel manual.
2. **Claim 2:**: Our axiomatic model, implemented in CBMC, is consistent with the traces provided in the Intel manual
3. **Claim 3**: Basic queue operations are validated against the operational model.
4. **Claim 4**: We were able to generate 583 disallowed traces and 153 allowed traces from the axiomatic model.
5. **Claim 5**: The Alloy-generated traces are consistent with the operational model.
6. **Claim 6**: The Alloy-generated traces are consistent with the hardware.
7. **Claim 7**: The corectly synchronised queue and the incorectly synchronised queues behave as expected. 

The frst 5 claims do not require any hardware while the last 2 claims require access to the IL Academic Compute Environment.

### Claim 1: Our operational model is consistent with the manual traces
We verify that the traces described in the manual are consistent with our CBMC implementation of the operational model. We have written the traces as C code that our CBMC implementation can interpret. The manual traces can be found in the following files:
1. [FPGA only traces](../model/CBMC/harp/tests_fpga.h)
2. [CPU-FPGA traces](../model/CBMC/harp/tests_cpu_fpga.h)

Each file presents the trace and points to the paragraph in the Intel manual where it is described. To verify all the traces against the operational model, run the following commands from the docker container:

```
    cd harpy/backend
    python3 backend.py --manual_traces 
```

Two parameters can be changed: the number of traces verified concurrently and the maximum unwind depth. To change the number of concurrent verifications, specify the `--cores` command-line argument, and change the unwind depth, specify the `--unwind` command-line argument.
For example, the following command runs the same experiment but uses 8 cores (instead of the deafault 4) and uses an unwind depth of 30 (instead of the default 8).

```
    python3 backend.py --manual_traces --cores 8 --unwind 30
```

#### Expected behaviour
This command will run all traces described in the manual and print a message if the traces were reproducible or not. This verification will take about two to three hours. All allowed traces should be reproducible, and all disallowed traces should not be reproducible.


### Claim 2: Our axiomatic model is consistent with the manual traces
We also verify that our Alloy implementation of the axiomatic model is consistent with the traces described in the manual and other manually generated traces. We have written the traces as code that our Alloy implementation can interpret. The manual traces can be found in the following [file](../model/alloy/traces.als). Because we do not explicitly claim this in the paper and because proving this requires software to be installed outside the docker container, this claim **can be skipped**.

Unfortunately, this can only be done via the Alloy GUI. For this reason, Alloy needs to be compiled outside the docker. To do this, ANT and JDK need to be installed. On a typical Ubuntu system, this can be done via the following commands:
```
    apt-get install openjdk-8-jdk 
    apt-get install ant 
```
Afterwards, Alloy can be compiled by executing the following commands:
```
    cd hapry
    git submodule update --init --recursive
    cd memalloy
    make -C alloystar
```

To start the Alloy GUI:
```
    cd harpy/memalloy/alloystar/dist
    chmod +x alloy4.2.jar
    ./alloy4.2.jar
```

Afterwards, open the [file](../model/alloy/traces.als) containing all the Alloy traces and from the **Execute menu**, click on **Execute All**. This will validate the axiomatic model with all the manually written Alloy traces.

#### Expected behaviour

After running the traces, we can expect that Alloy found an instance of the allowed behaviours but did not find any disallowed behaviours. This will be indicated by the Alloy solver reporting that the solution was "as expected".

![The result of validating Alloy with all the manually written traces](https://i.imgur.com/qm4Agze.png)


### Claim 3: The queue is validated against our operational model
We verify that disallowed queue operations cannot occur according to our operational model. Therefore we verify the enqueue and dequeue steps against our CBMC implementation. The file that presents the traces for these operations can be found [here](../model/CBMC/harp/tests_queue.h)

```
    cd backend
    python3 backend.py --queue_traces
```
#### Expected behaviour
CBMC should verify that the tested behaviour should not occur and that the disallowed behaviour cannot be reproduced.

### Claim 4: We were able to generate 583 disallowed traces and 153 allowed traces

We can use the axiomatic model to generate a large number of disallowed executions. The challenge here is that Alloy generates a significant amount of duplicate traces. To address this, we can run our script to eliminate these duplicates. Table 2 shows the total number of traces generated for each event count. To reproduce this table, the following steps are required:
```
    cd backend
    ./generate <#events>    # Alloy to generate all traces with #events
    python3 backend.py      # Removed duplicate traces  
```

#### Expected behaviour
After running this tool for 6 events, a message similar to this one will be displayed:
```
93 traces read
38 unique disallowed traces
2 unique allowed traces
```
This message indicates that Alloy generated 93 disallowed traces but after removing duplicates, only 38 were left. From these 38 disallowed traces, by removing fences, only 2 allowed traces were generated.

### Claim 5: The Alloy generated traces are consistent with the operational model
The previously generated traces can be verified in CBMC. However, doing so will take several days. Therefore, we recommend only verifying a subset of the allowed traces and a subset of the disallowed traces. 

Verifying the disallowed traces can be done using the following commands:
```
    cd backend
    ./generate <#events>
    python3 backend.py --cbmc --run_cbmc --max_traces 4

```
The `--cbmc` argument will make the script convert the alloy traces into CBMC code. The `--run_cbmc` parameter will make the script execute the CBMC code. The `--max_traces` parameter will limit the number of traces that will be verified. 

Verifying the allowed traces can be done using the following commands:
```
    cd backend
    ./generate <#events>
    python3 backend.py --cbmc --run_cbmc --fence -r --max_traces 4
```

The extra `--fence` argument will make the script remove fences, making the executions allowed. The `-r` argument will tell the script to expect that the traces to be reproducible.

#### Note

If you posses a machine with a large number of cores, and a significant amount of RAM, you can run more experiments concurrently by setting the ``---cores`` parameter to a higher number. However, the RAM requirements are quite high.

#### Expected behaviour
After all traces have been verified, the following message should appear
```
All traces could NOT be reproduced
```
or
```
All traces could be reproduced
```
depending on whether we were checking allowed executions or disallowed executions.


### **Claim 6**: The Alloy-generated traces are consistent with the hardware.



#### Synthesize the soft-core
After an account has been created for the IL Academic Compute Environment, the user should be able to connect with the following commands:

```
    ssh <username>@ssh-iam.intel-research.net                # Connect to the server    
    source /export/fpga/bin/setup-fpga-env fpga-bdx-opae     # Configure the environmental variables such that a Broadwell Xeon CPUs (E5-2600v4) with an integrated in-package Arria 10 is used
```
Afterwards, a local copy of the repo should be downloaded and the soft-core processor synthesized. This process will take about two hours but only needs to be done once.
```
    git clone https://github.com/diorga/harpy.git            
    cd harpy/backend/litmus_tests/test/hw
    afu_synth_setup -s rtl/sources.txt build_fpga    # Configure a synthesis project
    cd build_fpga    
    qsub-synth            # This will start the synthesis process
    tail -f build.log     # The file will report the build status
```    

When the processor is synthesized, the following message should appear:

```
=======================================================
 BDW 503 PR AFU compilation complete
 AFU gbs file located at litmus_processor.gbs
 Design meets timing
=======================================================
```

#### Upload traces to the server
Unfortunately, it is a bit tricky to install Alloy on the Intel server without root access. It will probably be easier to generate the traces locally and transfer them to the server using scp. This can be done with the following commands within the docker container.

```
    cd backend/
    ./generate <#events>
    scp -r traces <username>@ssh-iam.intel-research.net:/homes/<username>/harpy/backend
```

Depending on what ssh-key you used when registering to the IL Academic Compute Environment, you might need to first transfer the files from the docker to your local machine and then upload them to the server. 

To do so, first get the docker continer number using
```
 docker ps
```
Then copy the traces locally and upload them to the server 
```
    docker cp <containerId>:/usr/harpy/backend/traces .
    scp -r traces <username>@ssh-iam.intel-research.net:/homes/<username>/harpy/backend
```

#### Running the litmus tests

First connect to the Intel server and request an FPGA

```
    ssh <username>@ssh-iam.intel-research.net               # connect to the server        
    source /export/fpga/bin/setup-fpga-env fpga-bdx-opae    # set up ENV variables
    qsub-fpga                                               # request an fpga
```

The python script we used in previous claims requires a few extra packages. Because we do not have root access, we used a python virtual environment. Run the actual hardware tests using the following script
```
    cd harpy/backend
    source myenv/bin/activate        # Set up the virtual environment
    python3 backend.py --hardware --run_hardware
    deactivate                       # Dissable the virtual environment
```

The ``-hardware`` command line argument will tell the python script to generate litmus tests that will run on the CPU and FPGA. The ``--run_hardware`` command will tell the script to actuallly run the tests.

#### Expected behaviour

If no litmus tests exhibited weak behaviour, the following message should appear.

```
All hardware litmus test behaved as expected.
```

### **Claim 7**: The corectly synchronised queue and the incorectly synchronised queues

We analyse the behaviour of the queue in Figure 13 and Figure 14. Before the queues can be tested, they first need to be synthesised. This process is similar to the one for synthesizing the soft-core processor.

#### Synthesize the queues
After an account has been created for the IL Academic Compute Environment, the user should be able to connect with the following commands:

```
    ssh <username>@ssh-iam.intel-research.net               # Connect to the server         
    source /export/fpga/bin/setup-fpga-env fpga-bdx-opae    # Configure the environmental variables such that a Broadwell Xeon CPUs (E5-2600v4) with an integrated in-package Arria 10 is used
```
Afterwards, the queue can be synthesized. This process will take about two hours but only needs to be done once.
```
    cd harpy/case_study/queue/FPGA_enqueue/hw
    afu_synth_setup -s rtl/sources.txt build_fpga
    cd build_fpga
    qsub-synth            # This will start the synthesis process
    tail -f build.log     # The file will report the build status
```    

When the processor is synthesized, the following message should appear:

```
=======================================================
 BDW 503 PR AFU compilation complete
 AFU gbs file located at FPGA_enqueue.gbs
 Design meets timing
=======================================================
```

##### Note 
The exact same process needs to be done for the enqueue. Only the first command needs to be changed to the following:

```
    cd harpy/case_study/queue/FPGA_dequeue/hw/
```

#### Load the queue

First, connect to the Intel server and request a FPGA.
```
    ssh <username>@ssh-iam.intel-research.net            
    source /export/fpga/bin/setup-fpga-env fpga-bdx-opae
    qsub-fpga                                            # Request an FPGA
```

Load the enqueue image onto the FPGAL
```
    cd harpy/case_study/queue/FPGA_enqueue/hw/build_fpga
    fpgaconf FPGA_enqueue.gbs                            # Load the FPGA image
```

#### Compile the CPU code
This can be done quite straightforward using:
```
    cd harpy/case_study/queue/FPGA_enqueue/sw
    make
```

#### Run the synchornised queue 
Run the CPU/FPGA code
```
    ./FPGA_enqueue -e 1000000
```
This will start running the CPU code that will connect to the FPGA and set up the communication with it. Afterwards, the FPGA will attemp to send 1000000 elements to the CPU using the produer consumer queue described in section 7 of the paper. The number of elements sent can be changes by modyfing the ``-e `` parameter.

#### Expected behaviour
This will run the experiment described in Figure 13a for 1000000 elements. The final execution time should be then displayed.

![](https://i.imgur.com/sT0vfLx.png)

Since the queue is correctly synchronised, there should not be any wrong entries.


#### Run the improperly synchronised queue 

Run the CPU/FPGA code
```
    ./FPGA_enqueue --wr_rsp_enqueue 0 --wr_rsp_write_tail 0 -e 1000000
```
This will run the experiment and ommit both response synchronisation elements. This will most likely run faster than the correctly synchronised queue. However, the number of wrong entries will be quite low. To get more wrong entries, simillar to Figure 14a, we need to add more noise to the experiment. This can be done with the following command:
```
    ./FPGA_enqueue --wr_rsp_enqueue 0 --wr_rsp_write_tail 0 -e 1000000  --VL0_enemy 10
```
The `--VL0_enemy 10` command will tell the FPGA to add extra traffic on the VL0 channel every 10 clock cycles. Alternatively, noise can also be added to other channels such as VH0 and VH1.


#### Expected behaviour
This will run the experiment described in Figure 14a for 1000000 elements.  The final execution time and incorrectly received elements should be then displayed.

![](https://i.imgur.com/5aLELE6.png)

In our paper, we provided an upper bound for the number of incorrectly received elements. For this reason, it can be expected that in the actual experiments, a low number will be obatined.

##### Note

1. Adding more noise to the experiments will significantly increase the execution time of the experiment
2. Adding to much noise to the experiments makes the device prone to becoming unresponsive. We have reached out to Intel to make them aware of the problem

