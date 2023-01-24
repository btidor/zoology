FROM mcr.microsoft.com/vscode/devcontainers/base:0-jammy

COPY *.gpg /usr/share/keyrings/
COPY *.list /etc/apt/sources.list.d/

RUN apt-get update && export DEBIAN_FRONTEND=noninteractive \
    && apt-get -y upgrade \
    && apt-get -y install --no-install-recommends \
        nodejs python3-pip python3.11 yices2

RUN ln -sf /usr/bin/python3.11 /usr/bin/python3

RUN wget https://github.com/cvc5/cvc5/releases/latest/download/cvc5-Linux -O /usr/local/bin/cvc5 && \
    chmod +x /usr/local/bin/cvc5

RUN pip install black mypy pydocstyle
