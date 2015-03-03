NJSolver
====

A theorem prover for the Natural deduction Intuitionistic logic

## Overview

It proves given theorem and (if that is provable) outputs a PDF which contains proof diagram.

## Requirement

GHC, Parsec3, LaTeX, proof.sty

## Usage

    $ prove.sh theorem out[.pdf]

where the theorem is the form "a0, a1, ... , aN => p",
which operators and values are used:

* for conjunction: &
* disjunction: |
* implication: ->
* negation: ~
* false: F
* true: T

e.g. "~(p | q) => ~p | ~q", "=>(p&q->r)->p->q->r"

## Issues

* Quantifiers are not yet supported.
* The large proof diagram may be over the paper size.

