FROM debian:buster

MAINTAINER Pierre-Yves Strub <pierre-yves@strub.nu>

ENV DEBIAN_FRONTEND noninteractive

RUN \
	apt-get -q -y update && \
	apt-get -q -y dist-upgrade && \
	apt-get -q -y install sudo m4 rsync git && \
	apt-get -q -y --no-install-recommends install mccs ocaml-nox opam aspcud && \
	apt-get -q -y clean

COPY sudo-ci /etc/sudoers.d/ci

RUN addgroup --gid 2000 ci
RUN adduser --disabled-password --gecos "CI" --uid 2000 --gid 2000 ci
RUN chmod 440 /etc/sudoers.d/ci

USER    ci
WORKDIR /home/ci

ENV OPAMYES=true OPAMVERBOSE=0 OPAMJOBS=2 OPAMEXTERNALSOLVER=mccs

RUN \
	opam init --disable-sandboxing -a && \
	opam switch create -v docker ocaml-base-compiler.4.07.1 && \
	opam clean

RUN \
	opam repo add coq-released https://coq.inria.fr/opam/released

RUN \
	opam pin add -n coq 8.9.1 && \
	opam pin add -n coq-mathcomp-ssreflect 1.9.0 && \
	opam pin add -n finmap https://github.com/Nemeras/finmap.git && \
	opam install coq coq-mathcomp-field finmap && \
	opam clean
