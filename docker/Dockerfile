# The mathcomp/mathcomp images still ship dune 3.17, but the build needs
# dune >= 3.21 (native Rocq mode), hence the rocq/rocq-prover base image.
FROM rocq/rocq-prover:9.1.1

LABEL maintainer="Pierre-Yves Strub <pierre-yves@strub.nu>"

# Dependencies of Coq-Polyhedra; rocq-bignums is needed by enumeration/.
RUN \
	opam update -y && \
	opam install -y rocq-mathcomp-algebra rocq-mathcomp-finmap \
	  rocq-mathcomp-bigenough rocq-hierarchy-builder rocq-bignums && \
	opam clean -a -c -s --logs
