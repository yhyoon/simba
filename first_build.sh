#!/bin/bash

if [ ! -d "$HOME/.opam" ]
then
    opam init --auto-setup --disable-sandboxing --yes && opam clean
fi

if [ ! -d "$HOME/.opam/simba" ]
then
    opam switch create simba 4.12.0
fi

opam switch simba 
opam install --yes dune merlin ocaml-lsp-server dune-build-info batteries ocamlgraph core_kernel yojson containers-data containers z3

eval $(opam config env)

./build.sh

# NOTE: if z3 install failed, install z3.4.8.5 instead of latest
# opam install --yes z3.4.8.5
