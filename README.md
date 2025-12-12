<!---
This file was generated from `meta.yml`, please do not edit manually.
Follow the instructions on https://github.com/coq-community/templates to regenerate.
--->
# Attestation Maxims

[![Docker CI][docker-action-shield]][docker-action-link]

[docker-action-shield]: https://github.com/ku-sldg/attestation-maxims/actions/workflows/docker-action.yml/badge.svg?branch=main
[docker-action-link]: https://github.com/ku-sldg/attestation-maxims/actions/workflows/docker-action.yml




This library provides a formalization of attestation maxims in Rocq, enabling reasoning about cryptographic protocols and their security properties.

## Meta

- Author(s):
  - Will Thomas
  - Logan Schmalz
- License: [Creative Commons Attribution Share Alike 4.0 International](LICENSE)
- Compatible Rocq/Coq versions: 8.20 later
- Compatible OCaml versions: 4.12 or later
- Additional dependencies:
  - [RocqCandy](https://github.com/ku-sldg/rocq-candy)
  - [Equations](https://github.com/mattam82/Coq-Equations)
  - [Dune](https://dune.build) 3.17 or later
- Related publication(s): none

## Building and installation instructions

The easiest way to install the latest released version of Attestation Maxims
is via [OPAM](https://opam.ocaml.org/doc/Install.html):

```shell
opam repo add -a --set-default ku-sldg/opam-repo https://github.com/ku-sldg/opam-repo.git
opam repo add coq-released https://coq.inria.fr/opam/released
opam install rocq-attestation-maxims
```

To instead build and install manually, do:

``` shell
git clone https://github.com/ku-sldg/attestation-maxims.git
cd attestation-maxims
dune build
dune install
```



