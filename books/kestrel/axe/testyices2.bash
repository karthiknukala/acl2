#!/bin/bash

# Test script for Yices2 solver
#
# Copyright (C) 2026 Kestrel Institute
#
# License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
#
################################################################################

# This script should print "unsat" if Yices2 is being called correctly.

THISSCRIPTDIR="$( cd "$( dirname "$0" )" && pwd )"
cd "${THISSCRIPTDIR}"

echo "YICES2=${YICES2}"

./callyices2.bash testyices2.smt2 testyices2.out 10
cat testyices2.out
