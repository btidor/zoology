# syntax = btidor/syntax

FROM mcr.microsoft.com/devcontainers/base:noble

COPY *.sources /etc/apt/sources.list.d/
ADD --apt nodejs python3.12 python3.12-venv python3-pip

RUN pip3 install --break-system-packages ruff
