FROM gitpod/workspace-base

# Install dependencies
RUN sudo apt-get install -y build-essential curl libffi-dev libffi7 libgmp-dev libgmp10 libncurses-dev libncurses5 libtinfo5

# ghcup is a replacement for the haskell platform. It manages the development env easily.
# We use the official instalation script
RUN sudo curl --proto '=https' --tlsv1.2 -sSf https://get-ghcup.haskell.org | sh

# Env variables:
#   - Adds ghcup binaries to path
#   - set ghcup instalation script to non-interactive
#   - set ghcup instalation script to minimal instalation. That is: just install ghcup and nothing else
ENV PATH=${PATH}:${HOME}/.ghcup/bin
ENV BOOTSTRAP_HASKELL_NONINTERACTIVE=true
ENV BOOTSTRAP_HASKELL_MINIMAL=true

# Set up the environment. This will install the default versions of every tool.
RUN ghcup install ghc 9.4.4
RUN ghcup install hls
RUN ghcup install stack
RUN ghcup install cabal

# Latest version supported by HLS
RUN ghcup set ghc 9.4.4

# change stack's configuration to use system installed ghc.
# By default, stack tool will download its own version of the compiler,
# Setting up this configuration will avoid downloading haskell compiler twice.
# WARNING! Maybe this is not adecuate for your project! use your project wise stack.yaml to change this
RUN stack config set install-ghc --global false
RUN stack config set system-ghc --global true