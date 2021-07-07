
# Stage
FROM ubuntu:latest AS builder

RUN apt-get update && \
    apt-get install build-essential -y && \
    apt-get install python3 -y && \
    apt-get install -y python3-xmltodict && \
    apt-get install -y python3-tqdm && \
    apt-get install -y python3-termcolor && \
    apt-get install -y git && \
    apt-get install -y wget && \
    apt-get install -y tar && \
    apt-get install -y cbmc

# Install OpenJDK-8
RUN DEBIAN_FRONTEND="noninteractive" apt-get -y install tzdata
RUN apt-get update && \
    apt-get install -y openjdk-8-jdk && \
    apt-get install -y ant && \
    apt-get clean;
    
# Fix certificate issues
RUN apt-get update && \
    apt-get install ca-certificates-java && \
    apt-get clean && \
    update-ca-certificates -f;

# Setup JAVA_HOME -- useful for docker commandline
ENV JAVA_HOME /usr/lib/jvm/java-8-openjdk-amd64/
ENV JAVA_TOOL_OPTIONS=-Dfile.encoding=UTF8
RUN export JAVA_HOME
RUN export JAVA_TOOL_OPTIONS


# Configure Alloy*
WORKDIR /usr/harpy
RUN git clone https://github.com/johnwickerson/memalloy.git
WORKDIR /usr/harpy/memalloy
RUN git submodule update --init --recursive
RUN make -C alloystar


# Copy files
WORKDIR /usr/harpy
COPY model ./model
COPY backend ./backend 
COPY case_study ./case_study 
