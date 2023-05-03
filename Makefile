# -*- Makefile -*-

# --------------------------------------------------------------------
DUNEOPTS := --display=short

# --------------------------------------------------------------------
.PHONY: default build clean license

# --------------------------------------------------------------------
default: build
	@true

build:
	dune build $(DUNEOPTS)

clean:
	dune clean $(DUNEOPTS)

# --------------------------------------------------------------------
license:
	scripts/license COPYRIGHT.yaml theories/*.v

# --------------------------------------------------------------------
run-in-docker:
	docker run --rm -ti -v $$PWD:/home/ci/project \
	  coqpolyhedra/build-box opam config exec -- make -C project
