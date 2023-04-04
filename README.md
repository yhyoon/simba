# Simba

Simba(**S**ynthesis from **I**nductive specification e**M**powered by **B**idirectional **A**bstract interpretation)
is an inductive program synthesizer using forward and backward abstract interpretation for pruning search spaces.

## Dependencies

* [Xcode Command Line Tools](https://mac.install.guide/commandlinetools/4.html) and [Homebrew](https://brew.sh/index)

If you want to build and run this tool on macOS, you should install these tools first.

* `opam`(https://opam.ocaml.org/): for ocaml compiler
```sh
$ sudo apt-get install -y opam  # for linux
$ brew install opam  # for mac
$
$ opam init --auto-setup --disable-sandboxing --yes
```

* `libgmp-dev`(https://gmplib.org/): for z3 solver
```sh
$ sudo apt-get install -y libgmp-dev # for linux
$ brew install gmp # for mac
```

## Build

0. `TL;DR`, do it in one-line commannd

```sh
$ ./first_build.sh
```

1. Make proper ocaml environment and get dependency packages

```
opam switch create simba 4.12.0
opam switch simba 
opam install --yes dune merlin ocaml-lsp-server dune-build-info batteries ocamlgraph core_kernel yojson z3
```

### Required OPAM Packages
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

The compiled executable file can be found at ```_install/bin/simba```.
Since the executable is self-contained, it can be easily moved or copied to any location for your convenience and executed.

## Run the synthesizer

Just run the executable with target sl file.

```sh
$ ./simba.exe <options> [a SyGuS input file]
```

You may find the options available by:
```sh
$ ./simba.exe -help
```

For example, to solve the problem described in `testcases/bitvec/hd/hd-17-d5-prog.sl`,
```sh
$ simba/simba.exe testcases/bitvec/hd/hd-17-d5-prog.sl
````
You will get the following output:
```sh
(define-fun f ( (x (BitVec 64))) (BitVec 64) (bvand (bvneg (bvand (bvnot x) (bvneg x))) x))
****************** statistics *******************
size : 8
time : 1.24 sec
final max component size : 6
final component pool size : 4617
**************************************************
```

The first line shows a desirable solution (f is the target synthesis function), and the other lines show some useful statistics.

For more detailed progress log and statistics, use option `-log` as follows:
```sh
$ simba/simba.exe -log stdout bench/bitvec/hd/hd-17-d5-prog.sl
$ simba/simba.exe -log solving-hd-17-d5.log bench/bitvec/hd/hd-17-d5-prog.sl
````
