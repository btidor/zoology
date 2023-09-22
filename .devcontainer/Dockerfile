# syntax = btidor/syntax

FROM mcr.microsoft.com/vscode/devcontainers/base:0-jammy

COPY *.sources /etc/apt/sources.list.d/
ADD --apt nodejs python3.11 python3-pip

RUN ln -sf /usr/bin/python3.11 /usr/bin/python3
RUN pip install black pydocstyle
