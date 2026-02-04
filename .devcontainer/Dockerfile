# syntax = btidor/syntax

FROM mcr.microsoft.com/devcontainers/base:noble

COPY *.sources /etc/apt/sources.list.d/

ADD --apt libjemalloc2 nodejs python3.14-dev python3-pip
RUN ln -sf /usr/bin/python3.14 /usr/bin/python3 && \
rm -f /usr/bin/python3-config

ADD --apt libgmp-dev meson pkg-config
ADD https://github.com/bitwuzla/bitwuzla.git#b29041fbbe6318cb4c19a6e11c7616efc4cb4d32 /opt/bitwuzla
RUN cd /opt/bitwuzla && ./configure.py && \
    cd build && ninja install

RUN pip3 install --break-system-packages ruff
