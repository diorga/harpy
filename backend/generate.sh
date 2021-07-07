#!/bin/bash

# Clean previous traces
cd traces
rm *


# Generate new traces
cd ../../memalloy/alloystar/

if [ $# -ne 1 ]; 
then 
    PATH=$(pwd)/amd64-linux:$PATH java -Xmx3g -Djava.library.path=$(pwd)/amd64-linux -Dout=../../backend/traces -Dquiet=false -Dsolver=glucose -Dhigherorder=true -Dcmd=0 -Diter=true  edu/mit/csail/sdg/alloy4whole/RunAlloy ../../model/alloy/executions.als
else
    PATH=$(pwd)/amd64-linux:$PATH java -Xmx3g -Djava.library.path=$(pwd)/amd64-linux -Dout=../../backend/traces -Dquiet=false -Dsolver=glucose -Dhigherorder=true -Dcmd=0 -Diter=true  edu/mit/csail/sdg/alloy4whole/RunAlloy ../../model/alloy/executions"$1".als
fi
cd ../../backend/
