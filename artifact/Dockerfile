
# 1. Stage
FROM ubuntu:latest AS builder

RUN apt-get update && \
    apt-get install build-essential -y && \
    apt-get install python3 -y && \
    apt-get install -y python3-xmltodict && \
    apt-get install -y python3-termcolor && \
    apt-get install -y cbmc

WORKDIR /usr/harpy

COPY model ./model
COPY backend ./backend 
COPY case_study ./case_study 
