# OCaml2MCore

Welcome to the `ocaml2mcore` repository! The aim of this project is to provide a
translation from OCaml to MCore. The tool can also be used as an OCaml
source-to-source compiler by connecting it with the MCore OCaml compiler.

## Getting started

The `ocaml2mcore` tool requires the Miking `boot` package, which can be
installed using the following commands:

```bash
opam pin add boot https://github.com/miking-lang/miking.git#develop
opam install boot
```

The project uses a fork of the OCaml multicore compiler, included as a submodule
in the repository. To initiate the submodule, enter the following command:

```bash
git submodule update --init
```

To build the project and run the tests, enter:

```bash
make test
```

The executable is now in `build/ocaml2mcore`. To install the tool for the
current user, the command is:

```bash
make install
```

If you installed the tool, the following converts an OCaml hello world program
into an MCore program:

```
echo "print_endline \"Hello, world!\"" > test.ml
ocaml2mcore test.ml
```
