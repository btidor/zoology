FROM mcr.microsoft.com/vscode/devcontainers/base:0-jammy

COPY *.gpg /usr/share/keyrings/
COPY *.list /etc/apt/sources.list.d/

RUN apt update && apt -y upgrade

RUN apt -y install python3.11 python3.11-dev python3-pip
RUN ln -sf /usr/bin/python3.11 /usr/bin/python3

RUN apt -y install autoconf build-essential cmake default-jre gperf \
    libgmp3-dev python3-gmpy2 swig
RUN pip install cython pysmt
RUN sudo -u vscode -- pysmt-install --all --confirm-agreement

RUN apt -y install nodejs python3-pydot
RUN pip install black mypy pydocstyle
