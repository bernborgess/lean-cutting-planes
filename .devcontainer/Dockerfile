FROM mcr.microsoft.com/devcontainers/rust:1-1-bullseye

USER vscode
WORKDIR /home/vscode

RUN curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- -y 

ENV PATH="/home/vscode/.elan/bin:${PATH}"

# Documentation 
RUN cargo install mdbook
