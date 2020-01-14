MKDIR := $(dir $(realpath $(firstword $(MAKEFILE_LIST))))
BASEDIR := $(PWD)

.phony: %

%:
	cd $(MKDIR) && ocaml compiler.ml $(BASEDIR)/$@.scm > $@.s && nasm -f elf64 -o $@.o $@.s && gcc -static -m64 -o $@ $@.o && mkdir -p out && mv $@.o $@.s $@ out	
