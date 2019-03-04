%: Makefile.coq phony
	+make -f Makefile.coq $@

all: Categories/Makefile Makefile.coq
	+make -C Categories
	+make -f Makefile.coq all

clean: Makefile.coq
	+make -C Categories clean
	+make -f Makefile.coq clean
	rm -f Categories/Makefile
	rm -f Makefile.coq

Categories/Makefile:
	cd Categories && ./configure.sh

Makefile.coq: _CoqProject Makefile
	coq_makefile -f _CoqProject -o Makefile.coq INSTALLDEFAULTROOT = "."

_CoqProject: ;

Makefile: ;

phony: ;

.PHONY: all clean phony
