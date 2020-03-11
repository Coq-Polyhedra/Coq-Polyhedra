# -*- Makefile -*-

include Makefile.common

# --------------------------------------------------------------------
.PHONY: license dist run-in-docker

# --------------------------------------------------------------------
run-in-docker:
	docker run --rm -ti -v $$PWD:/home/ci/project \
	  coqpolyhedra/build-box opam config exec -- make -C project

# --------------------------------------------------------------------
license:
	scripts/license COPYRIGHT.yaml theories/*.v

# --------------------------------------------------------------------
DISTDIR := polyhedra
TAROPT  := --posix --owner=0 --group=0
TAR     ?= tar

dist:
	if [ -e $(DISTDIR) ]; then rm -rf $(DISTDIR); fi
	./scripts/distribution.py $(DISTDIR) MANIFEST
	BZIP2=-9 $(TAR) $(TAROPT) -cjf $(DISTDIR).tar.bz2 $(DISTDIR)
	rm -rf $(DISTDIR)
