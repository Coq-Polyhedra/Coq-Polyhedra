FROM mathcomp/mathcomp:2.6.0-rocq-prover-9.1

LABEL maintainer="Pierre-Yves Strub <pierre-yves@strub.nu>"

# Remaining dependencies of Coq-Polyhedra (MathComp and Hierarchy Builder
# come with the base image); rocq-bignums is needed by enumeration/.
RUN \
	opam update -y && \
	opam install -y rocq-mathcomp-finmap rocq-mathcomp-bigenough rocq-bignums && \
	opam clean -a -c -s --logs
