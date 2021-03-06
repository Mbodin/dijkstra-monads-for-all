
COQMAKEFILEOPTIONS ?= INSTALLDEFAULTROOT = "."

%: Makefile.coq phony
	+export HOME=`pwd`; make -f Makefile.coq $@

all: Makefile.coq
	+export HOME=`pwd`; make -f Makefile.coq all

clean: Makefile.coq
	+make -f Makefile.coq clean
	rm -f Makefile.coq

Makefile.coq: _CoqProject Makefile
	coq_makefile -f _CoqProject -o Makefile.coq $(COQMAKEFILEOPTIONS)

_CoqProject: ;

Makefile: ;

phony: ;

.PHONY: all clean phony

