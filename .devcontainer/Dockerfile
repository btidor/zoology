# syntax = btidor/syntax

FROM mcr.microsoft.com/devcontainers/base:noble

COPY *.sources /etc/apt/sources.list.d/
ADD --apt libjemalloc2 nodejs python3.13 python3-pip

RUN ln -sf /usr/bin/python3.13 /usr/bin/python3 && \
    rm -f /usr/bin/python3-config

RUN pip3 install --break-system-packages ruff
