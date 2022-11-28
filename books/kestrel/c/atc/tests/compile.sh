#!/usr/bin/env bash

################################################################################

# C Library
#
# Copyright (C) 2022 Kestrel Institute (http://www.kestrel.edu)
#
# License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
#
# Author: Alessandro Coglio (coglio@kestrel.edu)

################################################################################

# This file compiles all the C files generated by ATC
# and all the handwritten test harness ATC files.

# This file assumes that GCC is in the path,
# as should be gnerally the case for macOS and Linux.

################################################################################

# stop on error:
set -e

# generate binaries:
gcc -o arrays arrays.c arrays-test.c
gcc -o assign assign.c assign-test.c
gcc -o calls calls.c calls-test.c
gcc -o checksum checksum.c checksum-test.c
gcc -o conditionals conditionals.c conditionals-test.c
gcc -o constants constants.c constants-test.c
gcc -o conversions conversions.c conversions-test.c
gcc -o int int.c int-test.c
gcc -o locvars locvars.c locvars-test.c
gcc -o loops loops.c loops-test.c
gcc -o mbt mbt.c mbt-test.c
gcc -o nonstrict nonstrict.c nonstrict-test.c
gcc -o not not.c not-test.c
gcc -Wno-logical-not-parentheses -o operators operators.c operators-test.c
gcc -o ops-diff-types ops-diff-types.c ops-diff-types-test.c
gcc -o structs structs.c structs-test.c
gcc -o ext-objs ext-objs.c ext-objs-test.c
