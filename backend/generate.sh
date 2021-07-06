#!/bin/bash

cd traces

cd ~/workspace/memalloy/alloystar
PATH=/home/dan/workspace/memalloy/alloystar/amd64-linux:$PATH java -Xmx3g -Djava.library.path=/home/dan/workspace/memalloy/alloystar/amd64-linux -Dout=/home/dan/workspace/harpy/backend/traces -Dquiet=false -Dsolver=glucose -Dhigherorder=true -Dcmd=0 -Diter=true  edu/mit/csail/sdg/alloy4whole/RunAlloy /home/dan/workspace/harpy/model/alloy/executions.als
cd ~/workspace/harpy/backend
