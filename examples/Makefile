# makefile to produce the TIP benchmarks

HS_FILES = $(wildcard *.hs)
POLY_FILES = $(addprefix poly/,$(subst .hs,.smt2,$(HS_FILES)))

all: all_smbc all_hbmc

all_smbc: poly $(POLY_FILES)
	mkdir -p output
	for i in poly/*.smt2 ; do \
	  mkdir -p output/`basename $$i .smt2` ; \
	  echo "convert $$i" ; \
	  tip --type-skolem-conjecture --monomorphise --split-conjecture "$$i" output/`basename $$i .smt2` ; \
	done

all_hbmc: poly $(POLY_FILES)
	mkdir -p hbmc_output
	for i in poly/*.smt2 ; do \
	  mkdir -p hbmc_output/`basename $$i .smt2` ; \
	  echo "convert $$i" ; \
	  tip --split-conjecture "$$i" hbmc_output/`basename $$i .smt2` ; \
	done

clean:
	rm -rf output hbmc_output poly *.dyn* *.hi *.o

poly:
	mkdir -p poly

poly/%.smt2: %.hs
	tip-ghc $< > $@


.PHONY: all clean poly
