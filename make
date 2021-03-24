#!/bin/sh

# Forces the script to exit on error
set -e

# Build the OCaml compiler
build_ocaml() {
    cd ocaml-multicore
    if [ ! -f utils/config.ml ]; then
        ./configure
    fi
    make -j $(( $nproc + 1 ))
    cd ..
}

# Build the project
build() {
    if [ ! -d build ]; then
        mkdir -p build

        cp -r ocaml-multicore/utils/*.ml* \
              ocaml-multicore/driver/compmisc.ml* \
              ocaml-multicore/driver/compenv.ml* \
              ocaml-multicore/file_formats/*.ml* \
              ocaml-multicore/parsing/*.ml* \
              ocaml-multicore/boot/menhir/*.ml* \
              ocaml-multicore/typing/*.ml* \
              ocaml-multicore/lambda/*.ml* \
              build

        rm build/camlinternalMenhirLib.ml*
        rm build/parser.mli

        echo \
            "(executable
              (name main)
              (libraries boot)
              (modules_without_implementation
               annot
               asttypes
               cmo_format
               cmx_format
               cmxs_format
               outcometree
               parsetree))" > build/dune

        echo "(lang dune 2.8)" > build/dune-project
    fi

    cp src/*.ml* build

    cd build; dune build --profile release; cd ..

    cp -f build/_build/default/main.exe build/ocaml2mcore
}

# Install ocaml2mcore locally for the current user
install() {
    bin_path=$HOME/.local/bin/
    lib_path=$HOME/.local/lib/mcore/ocaml2mcore
    mkdir -p $bin_path $lib_path
    cp -f build/ocaml2mcore $bin_path/ocaml2mcore; chmod +x $bin_path/ocaml2mcore
}

# Run the tests
run_tests() {
    echo "--- String comparison tests ---"
    cd test/string-compare; fish grader.fish ../../build/ocaml2mcore 2> .log; cd ../..
    echo "--- Tests evaluating MCore output ---"
    cd test/eval; fish grader.fish fish runner.fish ../../build/ocaml2mcore 2> .log; cd ../..
    echo "--- Source-to-source compilation tests ---"
    cd test/source2source; fish grader.fish fish runner.fish ../../build/ocaml2mcore 2> .log; cd ../..
}

clean() {
    rm -rf build
}

case $1 in
    ocaml)
        build_ocaml
        ;;
    build)
        build
        ;;
    install)
        install
        ;;
    test)
        build
        run_tests
        ;;
    lint)
        cd src; dune build @fmt --auto-promote; cd ..
        ;;
    clean)
        clean
        ;;
    veryclean)
        clean
        cd ocaml-multicore; make clean; cd ..
        ;;
    all | *)
        build_ocaml
        build
        ;;
esac
