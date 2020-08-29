FROM p4lang/p4c:latest

ARG DEBIAN_FRONTEND=noninteractive

# Install dependencies.
RUN apt-get update
RUN apt-get install -y --no-install-recommends \
  wget \
  ca-certificates \
  build-essential \
  python3 \
  libgmp-dev \
  git
RUN update-ca-certificates

# Install g++-8 for -std=17 with structural binding.
RUN apt-get install -y g++-8
RUN update-alternatives --install /usr/bin/gcc gcc /usr/bin/gcc-8 60 --slave /usr/bin/g++ g++ /usr/bin/g++-8
RUN update-alternatives --config gcc

COPY . /p4-symbolic/
WORKDIR /p4-symbolic/

RUN wget "https://github.com/bazelbuild/bazelisk/releases/download/v1.4.0/bazelisk-linux-amd64"
RUN chmod +x bazelisk-linux-amd64
RUN ln -s $(pwd)/bazelisk-linux-amd64 /usr/local/bin/bazel
