FROM mcr.microsoft.com/vscode/devcontainers/base:0-jammy

COPY *.gpg /usr/share/keyrings/
COPY *.list /etc/apt/sources.list.d/

RUN apt update && apt -y upgrade

RUN apt -y install python3.11 python3.11-dev python3-pip
RUN ln -sf /usr/bin/python3.11 /usr/bin/python3

RUN pip install cython && \
    apt -y install build-essential cmake libgmp3-dev
RUN git clone https://github.com/bitwuzla/bitwuzla && \
    cd bitwuzla && \
    ./contrib/setup-cadical.sh && \
    ./contrib/setup-btor2tools.sh && \
    ./contrib/setup-symfpu.sh && \
    ./configure.sh --python && \
    cd build && make && make install && \
    mv /usr/local/lib/pybitwuzla.so /usr/lib/python3/dist-packages/ && \
    ldconfig

RUN apt -y install nodejs
RUN pip install black pydocstyle
