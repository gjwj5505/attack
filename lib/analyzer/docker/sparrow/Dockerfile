FROM ocaml/opam:ubuntu-20.04-ocaml-4.05

SHELL ["/bin/bash", "-lc"]

USER root

RUN apt-get update && apt-get install -y --no-install-recommends \
    build-essential \
    ca-certificates \
    git \
    libgmp-dev \
    libmpfr-dev \
    m4 \
    pkg-config \
    python2 \
    unzip \
    wget \
    && rm -rf /var/lib/apt/lists/*

RUN mkdir -p /opt/sparrow && chown -R opam:opam /opt/sparrow

USER opam

RUN git clone https://github.com/ropas/sparrow.git /opt/sparrow

WORKDIR /opt/sparrow

RUN printf '%s\n' \
    'open Cil' \
    '' \
    'type featureDescr = {' \
    '  fd_name : string;' \
    '  mutable fd_enabled : bool;' \
    '  fd_description : string;' \
    '  fd_extraopt : (string * Arg.spec * string) list;' \
    '  fd_doit : Cil.file -> unit;' \
    '  fd_post_check : bool;' \
    '}' \
    '' \
    'let enabled _ = false' \
    > src/util/feature.ml

RUN opam repository add archive git+https://github.com/ocaml/opam-repository-archive --all-switches && \
    opam update && \
    opam pin add yojson 1.7.0 -y && \
    opam pin add ocamlgraph 1.8.8 -y && \
    opam install . --deps-only -y

RUN eval "$(opam env)" && make

ENV SPARROW_HOME=/opt/sparrow
ENV PATH="/opt/sparrow/bin:${PATH}"

WORKDIR /work

ENTRYPOINT ["/opt/sparrow/bin/sparrow"]
