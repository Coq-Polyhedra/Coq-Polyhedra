# -*- Makefile -*-

include Makefile.common

# --------------------------------------------------------------------
DISTDIR := polyhedra
TAROPT  := --posix --owner=0 --group=0
TAR     ?= tar

dist:
	if [ -e $(DISTDIR) ]; then rm -rf $(DISTDIR); fi
	./scripts/distribution.py $(DISTDIR) MANIFEST
	BZIP2=-9 $(TAR) $(TAROPT) -cjf $(DISTDIR).tar.bz2 $(DISTDIR)
	rm -rf $(DISTDIR)
