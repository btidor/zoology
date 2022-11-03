FROM mcr.microsoft.com/vscode/devcontainers/base:0-jammy

COPY *.gpg /usr/share/keyrings/
COPY *.list /etc/apt/sources.list.d/

RUN apt-get update && export DEBIAN_FRONTEND=noninteractive \
    && apt-get -y upgrade \
    && apt-get -y install --no-install-recommends \
        nodejs python3.9 python3.9-distutils python3.9-dev yices2

COPY get-pip.py /tmp
RUN python3.9 /tmp/get-pip.py

RUN pip3.9 install black manticore protobuf==3.20.3
