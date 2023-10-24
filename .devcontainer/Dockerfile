# syntax = btidor/syntax

FROM mcr.microsoft.com/vscode/devcontainers/base:0-jammy

COPY *.sources /etc/apt/sources.list.d/
ADD --apt nodejs python3.12 python3.12-venv
RUN ln -sf /usr/bin/python3.12 /usr/bin/python3 && \
    python3.12 -m ensurepip

RUN pip3 install ruff
