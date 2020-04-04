# -*- Makefile -*-

# --------------------------------------------------------------------
SCRIPT  := ./extract.py
TARGETS ?= poly20dim21

# --------------------------------------------------------------------
.PHONY: all clean clean
.PRECIOUS: %.done %.tbz2

all: $(TARGETS:%=%.tbz2)

clean:
	rm -rf $(TARGETS:%=%.done) $(TARGETS:%=%.tbz2) $(TARGETS)

%.done: $(SCRIPT) %.ext %.ine
	rm -rf $*.done $*; $(SCRIPT) $* && touch $@

%.tbz2: %.done
	tar -cj --options bzip2:compression-level=9 -f $@ $*
