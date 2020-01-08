<<<<<<< HEAD
MKDIR := $(dir $(realpath $(firstword $(MAKEFILE_LIST))))
BASEDIR := $(PWD)

.phony: %

%:
	cd $(MKDIR) && ocaml compiler.ml $(BASEDIR)/$@.scm > $@.s && nasm -f elf64 -o $@.o $@.s && gcc -static -m64 -o $@ $@.o && mv $@ $(BASEDIR)
=======
MKDIR := $(dir $(realpath $(firstword $(MAKEFILE_LIST))))
BASEDIR := $(PWD)

.phony: %

%:
	cd $(MKDIR) && ocaml compiler.ml $(BASEDIR)/$@.scm > $@.s && nasm -f elf64 -o $@.o $@.s && gcc -static -m64 -o $@ $@.o && mv $@ $(BASEDIR)
>>>>>>> 173d4d775e13d1044401a72be41bf1db4d7d77f3
