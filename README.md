# The Semantics of Shared Memory in Intel CPU/FPGA Systems

This repo focuses on the semantics of shared memory in heterogeneous CPU/FPGA systems. Here, we focus on the CCI-P interface and describe 
the operational and axiomatic semantics. We mechanised each in a model checker and validated the models against each other and the actual hardware. 
We use our model to reason about a producer/consumer queue.

## Repo structure
### Dockerfile
* [The docker container ](artifact/)

### Model
* [CBMC Model](model/CBMC/harp/)
* [Alloy Model](model/alloy)

### Queue implementation 
* [Case_study ](case_study/)

## Hardware experiments
Setting up the environment:

```
ssh <username>@ssh-iam.intel-research.net
source /export/fpga/bin/setup-fpga-env fpga-bdx-opae
```

# Simulation

```
qsub-sim
cd hw
afu_sim_setup -s rtl/sources.txt build_sim
tmux
# Compile and run the RTL simulator
cd build_sim
make
make sim
```

# Synthesizing

```
# Configure a Quartus build area
afu_synth_setup -s rtl/sources.txt build_fpga
cd build_fpga
# Run Quartus in the vLab batch queue
qsub-synth
# Monitor the build (the file is created after the job starts)
tail -f build.log
```
