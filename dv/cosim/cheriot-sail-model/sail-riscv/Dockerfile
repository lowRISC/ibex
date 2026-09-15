FROM ocaml/opam
USER root
RUN DEBIAN_FRONTEND=noninteractive apt-get -y install zlib1g-dev pkg-config libgmp-dev z3
USER opam
RUN opam install sail
