
.PHONY : all build ocaml test lint clean veryclean

all:
	@./make

ocaml:
	@./make ocaml

build:
	@./make build

install:
	@./make install

test:
	@./make test

lint:
	@./make lint

clean:
	@./make clean

veryclean:
	@./make veryclean
