# Notes on devcontainer.json and Docker file:
# The only thing that might be useful to change in the devcontainer.json file is
# the remote user name. One is haseller and the other one is VSCode.
# For Dockerfile, I'll leave comments beginning with NOTE to point out where it
# could be useful to examine.

# NOTE: the first issue is the base Dockerfile. One is from the VSCode generated
# Dockerfile, and the other one is a Dockerfile in here:
# https://github.com/vzarytovskii/haskell-dev-env
# The VSCode one will set up the vscode user, and the other ones don't.
# But the VSCode one seems to install more useful packages like vi.

# See here for image contents: https://github.com/microsoft/vscode-dev-containers/tree/v0.177.0/containers/debian/.devcontainer/base.Dockerfile

# [Choice] Debian version: buster, stretch
ARG VARIANT="buster"
FROM mcr.microsoft.com/vscode/devcontainers/base:0-${VARIANT}

# ** [Optional] Uncomment this section to install additional packages. **
# RUN apt-get update && export DEBIAN_FRONTEND=noninteractive \
#     && apt-get -y install --no-install-recommends <your-package-list-here>

# NOTE: This is the debian Dockerfile
# FROM debian:stable

ARG GHC_VERSION=8.10.4
ARG STACK_RESOLVER=lts-17.7

# NOTE: The second problem is about the user. With VSCode's base Dockerfile, it
# will produce the best but not perfect result, and in that case the remote user
# is haskeller. But because of that, it could be that the cabal is installed in
# haskeller's home address while actually the working directory, and where the
# hls project has been placed, is under the vscode's directory.

# NOTE: If I change the base to Debian's, remote user to haskeller, so that
# there does not exist a user called vscode, then what we have to focus on is
# is the privilege of the haskeller user. But it has the following issue:
# When I run `./cabal-hls-install hls`, it will call out an error saying that
# the permission is denied. I guess it is an error of privilege. This is with
# base Dockerfile Debian's, user haskeller. I can use sudo to run the command,
# but it says cabal will not be found. I have searched on Stackoverflow, it
# basically said that this is because issue of sudo, not of cabal. Nevertheless,
# I didn't found a way to resolve this. And the whole mess could still back to
# the problem of, how to set up an user properly.

ENV USERNAME=haskeller \
    USER_UID=2001 \
    USER_GID=2001 \
    DEBIAN_FRONTEND=noninteractive \
    GHC_VERSION=${GHC_VERSION} \
    STACK_RESOLVER=${STACK_RESOLVER}

RUN apt-get update
RUN apt-get install -y --no-install-recommends git curl xz-utils gcc make libtinfo5 libgmp-dev zlib1g-dev bash sudo procps lsb-release ca-certificates build-essential curl libffi-dev libffi6 libgmp-dev libgmp10 libncurses-dev libncurses5 libtinfo5 libicu-dev libncurses-dev z3

RUN groupadd --gid $USER_GID $USERNAME && \
    useradd -ms /bin/bash -K MAIL_DIR=/dev/null --uid $USER_UID --gid $USER_GID -m $USERNAME && \
    echo $USERNAME ALL=\(root\) NOPASSWD:ALL > /etc/sudoers.d/$USERNAME && \
    chmod 0440 /etc/sudoers.d/$USERNAME


# NOTE: The final note for this Dockerfile, then has to arrive to the privilege issue.
# The commands above, seems to set up the privilege of the user. I remember that
# the groupadd is annoying when I make the user to be only the vscode one. Anyways
# I never figured out why I might stuck at these commands, and maybe how to
# separate them apart to analyze. Its original purpose is adding haskeller to a
# group called haskeller. I have tried to add the haskeller user to root, but I
# failed.

USER ${USER_UID}:${USER_GID}
WORKDIR /home/${USERNAME}
ENV PATH="/home/${USERNAME}/.local/bin:/home/${USERNAME}/.cabal/bin:/home/${USERNAME}/.ghcup/bin:$PATH"

RUN echo "export PATH=$PATH" >> /home/$USERNAME/.profile

ENV BOOTSTRAP_HASKELL_NONINTERACTIVE=yes \
    BOOTSTRAP_HASKELL_NO_UPGRADE=yes

RUN curl --proto '=https' --tlsv1.2 -sSf https://get-ghcup.haskell.org | sh

# Check if needed GHC_VERSION was already installed during bootstrap, otherwise - install it.
RUN echo "Checking, whether GHC(${GHC_VERSION}) is already installed" && \
    if ghcup list 2>&1 | sed -r "s/\x1B\[([0-9]{1,3}(;[0-9]{1,2})?)?[mGK]//g" | grep -P "\xE2\x9C\x94\sghc\s+${GHC_VERSION}\s+\w+" ; \
    then \
        echo "GHC ${GHC_VERSION} is already installed via ghcup." ; \
    else \
        echo "GHC ${GHC_VERSION} was not found. Installing via ghcup." && \
        ghcup install ghc ${GHC_VERSION} ; \
    fi

# Set the GHC version.
RUN ghcup set ghc ${GHC_VERSION}

# Install cabal-iinstall
RUN ghcup install cabal

# Update Cabal.
RUN cabal update
RUN cabal new-install cabal-install

# Configure cabal
RUN cabal user-config update -f && \
    sed -i 's/-- ghc-options:/ghc-options: -haddock/g' ~/.cabal/config

# Install stack
RUN curl -sSL https://get.haskellstack.org/ | sh

# Init global-project.
RUN ((stack ghc -- --version 2>/dev/null) || true)

# Set system-ghc, install-ghc and resolver for stack.
RUN stack config --system-ghc set system-ghc --global true && \
    stack config --system-ghc set install-ghc --global false && \
    stack config --system-ghc set resolver $STACK_RESOLVER

# Set global custom defaults for stack.
RUN printf "ghc-options:\n  \"\$everything\": -haddock\n" >> /home/${USERNAME}/.stack/config.yaml

# Dependencies for HLS
RUN sudo apt install libicu-dev libncurses-dev libgmp-dev zlib1g-dev

ENV PATH="$PATH:/home/haskeller/.cabal:/home/haskeller/.cabal/bin"

# Is it necessary?
# RUN cabal install ghcide --global
# RUN cabal v2-run /workspace/haskell-language-server/install.hs --project-file install/shake.project <target>



ENV DEBIAN_FRONTEND=dialog

ENTRYPOINT ["/bin/bash"]
