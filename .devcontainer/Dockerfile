FROM mcr.microsoft.com/vscode/devcontainers/base:0-jammy

COPY *.gpg /usr/share/keyrings/
COPY *.list /etc/apt/sources.list.d/

RUN apt update && apt -y upgrade

RUN apt -y install python3.11 python3.11-dev python3-pip
RUN ln -sf /usr/bin/python3.11 /usr/bin/python3

RUN apt -y install build-essential cmake libgmp3-dev
RUN git clone https://github.com/bitwuzla/bitwuzla && \
    cd bitwuzla && \
    ./contrib/setup-cadical.sh && \
    ./contrib/setup-btor2tools.sh && \
    ./contrib/setup-symfpu.sh && \
    ./configure.sh && cd build && make && make install

RUN pip install pysmt
# Bitwuzla can't handle this set-option command
RUN sed -i '/set_option.*diagnostic-output-channel/d' \
    /usr/local/lib/python3.11/dist-packages/pysmt/smtlib/solver.py
# Free performance!
RUN sed -i '/time.sleep.0.01./d' \
    /usr/local/lib/python3.11/dist-packages/pysmt/smtlib/solver.py

RUN apt -y install nodejs
RUN pip install black mypy pydocstyle
