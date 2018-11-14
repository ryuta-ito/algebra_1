#!/bin/sh -eux

coqc set.v
coqc group.v
coqc relation.v
coqc homomorphism.v
coqc coset.v
