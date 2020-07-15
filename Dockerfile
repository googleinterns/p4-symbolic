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

# Install Z3.
RUN git clone https://github.com/Z3Prover/z3.git /z3
WORKDIR /z3/
RUN git checkout ad55a1f1c617a7f0c3dd735c0780fc758424c7f1  # Latest release.
RUN python scripts/mk_make.py
RUN cd build && make -j4 && make install

COPY . /p4-symbolic/
WORKDIR /p4-symbolic/

RUN wget "https://github.com/bazelbuild/bazelisk/releases/download/v1.4.0/bazelisk-linux-amd64"
RUN chmod +x bazelisk-linux-amd64
RUN ln -s $(pwd)/bazelisk-linux-amd64 /usr/local/bin/bazel
