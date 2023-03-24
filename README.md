# Simba

Simba(Synthesis from Inductive specification eMpowered by Bidirectional Abstract interpretation)
is an inductive program synthesizer that combines top-down deduction and bottom-up enumeration
and do abstract interpretation for pruning.

## Dependencies

If you use lesser version of these tools, success of build or execution is not guaranteed.

* OPAM >= 2.1.2
* libgmp

## Build

1. Make proper ocaml environment and get dependency packages

```
opam switch create simba 4.12.0
opam switch simba 
opam install --yes dune merlin ocaml-lsp-server dune-build-info batteries ocamlgraph core_kernel yojson z3
```

### Libraries
* `dune` : build system
* `dune-build_info` : insert version information(commit id) to binary
* `merlin` : IntelliSense system
* `ocaml-lsp-server`: for merlin in visual studio code
* `batteries` : extended standard libraries
* `ocamlgraph` : ordering grammar rules
* `core-kernel` : sexp utilities
* `yojson` : report by json format
* `z3` : SMT solver

2. Build by dune
```
dune build
dune install --prefix=_install
```

Now executable file is at ```_install/bin/simba```

## Run the synthesizer

Just run the executable with target sl file. `-help` option will be `help`ful. :)
