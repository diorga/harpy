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

From within the git repo, build the docker image

```
docker build -t diorga/harpy -f artifact/Dockerfile .
```

Next, start the docker container

```
docker run -it diorga/harpy bash
```

This should start a docker container where all the experiments can be run.

#### Note

Depending on how you installed docker, you might need to prefix every docker command with **sudo**.

### Testing CBMC + Alloy
To verify that everything has been configured properly, run the following commands. 
```
    cd backend
    ./generate 4
    python3 backend.py --cbmc --run_cbmc --max_traces 2
```
This will use Alloy to generate all disallowed traces with 4 events . Afterwards, CBMC will verify 2 just two of them. After this, a message that the traces could not be reproduced by the model will be displayed. 

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
4. **Claim 4**: We were able to generate 477 disallowed traces and 183 allowed traces from the axiomatic model.
5. **Claim 5**: The Alloy-generated traces are consistent with the operational model.
6. **Claim 6**: The Alloy-generated traces are consistent with the hardware.
7. **Claim 7**: The corectly synchronised queue and the incorectly synchronised queues behave as expected. 

The frst 5 claims do not require any hardware while the last 2 claims require access to the IL Academic Compute Environment.

### Claim 1: Our operational model is consistent with the manual traces
We verify that the traces described in the manual are consistent with our CBMC implementation of the operational model. We have written the traces as C code that can be interpreted by our CBMC implementation. The manual traces can be found in the following files:
1. [FPGA only traces](../model/CBMC/harp/tests_fpga.h)
2. [CPU-FPGA traces](../model/CBMC/harp/tests_cpu_fpga.h)

Each file presents the trace and points to the paragraph in the Intel manual where it is described. To verify all the traces against the operational model, run the following commands from the docker container:

```
    cd harpy/backend
    python3 backend.py --manual_traces 
```

There are two parameters that can be changed at this stage: the number of traces that will be verified concurently, and the maximum unwind depth. To change the number of concurent verifications, specify the `--cores` command line argument and to change the unwind depth, specify the `--unwind` command line argument.

For example, the following command runs the same experiment but uses 8 cores instead of 4 and uses an unwind depth of 30.

```
    python3 backend.py --manual_traces --cores 8 --unwind 30
```

#### Expected behaviour
This will run all traces described in the manual and print a message if the traces were reproducible or not. This entire verification will take about two to three hours. The expected behaviour is that all allowed traces should be reproducible and all disallowed traces should not be reproducible.


### Claim 2: Our axiomatic model is consistent with the manual traces
We also verify that our Alloy implementation of the axiomatic model is consistent with the traces described in the manual and other manually generated traces. We have written the traces as code that can be interpreted by our Alloy implementation. The manual traces can be found in the following [file](../model/alloy/traces.als). Because this claim is not explicitly stated in the paper and also requires installing of additional software on the host machine, it can be skipped.

Unfortunately, this can only be done via the Alloy GUI. For this reason, Alloy needs to be compiled outside the docker. To do, this, ANT and JDK need to be installed. On a tipical Ubuntu system, this can be done via the following commands:
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

To start the Alloy guy:
```
    cd harpy/memalloy/alloystar/dist
    chmod +x alloy4.2.jar
    ./alloy4.2.jar
```

Afterwards open the [file](../model/alloy/traces.als) containing all the Alloy traces and from the **Execute menu**, click on **Execute All**. This will validate the axiomatic model with all the manually written Alloy traces.

#### Expected behaviour

After running the traces, we can expect that Alloy found an instance of the allowed behaviours but did not find any instance of disallowed behaviours. This will be indicated by the Alloy solver reporting that the solution was "as expected".

![The result of validating Alloy with all the manually written traces](https://i.imgur.com/qm4Agze.png)




### Claim 3: The queue is validated against our operational model
We take a similar approach to verify that disallowed queue operations cannot occur according to our operational model. Therefore we verify enqueue and dequeue against our CBMC implementation. The file that presents the traces for these operations can be found [here](../model/CBMC/harp/tests_queue.h)

```
    cd backend
    python3 backend.py --queue_traces
```
#### Expected behaviour
CBMC should verify that the tested behaviour should not occur and the disallowed behaviour cannot be reproduced.

### Claim 4: We were able to generate 477 disallowed traces and 183 allowed traces

We can use the axiomatic model to generate a large number of disallowed executions. The challenge here is that Alloy generates a significant amount of duplicate traces. To address this, we can run our script to eliminate these duplicates. Table 2 shows the total number of traces generated for each event count. To reproduce this table, the following steps are required
```
    cd backend
    ./generate <#events>    # Alloy to generate all traces with #events
    python3 backend.py      # Removed duplicate traces  
```

#### Expected behaviour
After running this tool for 6 events, a message similar to this one will be displayed.
```
59 traces read
21 unique disallowed traces
2 unique disallowed traces
```
This indicates that Alloy generated 10 traces but one of them was a duplicate.

### Claim 5: The Alloy generated traces are consistent with the operational model
The previously generated traces can be verified in CBMC. However, doing so will take several days. I recommend only verifying a subset of the allowed traces and a subset of the disallowed traces. 

To verify the number of disallowed traces, the following command needs to be executed.
```
    cd backend
    ./generate <#events>
    python3 backend.py --cbmc --run_cbmc --max_traces 4

```
The `--cbmc` argument will make the script convert the alloy traces into CBMC code. The `--run_cbmc` parameter will make the script execute the CBMC code. The `--max_traces` parameter will limit the number of traces that will be verified. 

To verify the number of allowed traces, the following command needs to be executed.
```
    cd backend
    ./generate <#events>
    python3 backend.py --cbmc --run_cbmc --fence -r --max_traces 4
```

The extra `--fence` argument will make the script remove fences, making the executions allowed. The `-r` argument will tell the script to expect that the traces to be reproducible.

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
    ssh <username>@ssh-iam.intel-research.net            
    source /export/fpga/bin/setup-fpga-env fpga-bdx-opae
```
Afterwards, a local copy of the repo should be downloaded and the soft-core processor synthesized. This process will take about two hours but only needs to be done once.
```
    git clone https://github.com/diorga/harpy.git
    cd harpy/backend/litmus_tests/test/hw
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
Unfortunately, it is a bit tricky to install Alloy on the Intel serve. It will probably be easier to generate the traces locally and transfer them to the server using scp. This can be done with the following commands within the docker container.

```
    cd backend/
    ./generate <#events>
    scp -r traces <username>@ssh-iam.intel-research.net:/homes/<username>/harpy/backend
```

Depending on what ssh-key you used when registering to the IL Academic Compute Environment, you might need to first transfer the files from the docker to your local machine and then upload them to the sever. 

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

Run the actual hardware tests using the following script
```
    cd harpy/backend
    source myenv/bin/activate
    python3 backend.py --hardware --run_hardware
```

The **-hardware** command line argument will tell the python script to generate litmus tests that will runon the CPU and FPGA. The **--run_hardware** command will tell the script to actuallly run the tests.
