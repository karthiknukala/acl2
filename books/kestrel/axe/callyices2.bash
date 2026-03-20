#!/bin/bash

# A script to call the Yices2 SMT-LIB2 solver.
#
# Copyright (C) 2026 Kestrel Institute
#
# License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
#
################################################################################

set -e

if [ $# -ne 3 ]
then
    echo "callyices2.bash: ERROR: Arguments must be the input file, output file, and timeout seconds (-1 for no timeout)."
    exit 1
fi

INPUT_FILE=$1
OUTPUT_FILE=$2
TIMEOUT_SECS=$3

YICES2=${YICES2:-yices-smt2}

if ! command -v "${YICES2}" >/dev/null 2>&1 ; then
    exit 201
fi

if [ "${TIMEOUT_SECS}" = "-1" ] ; then
    "${YICES2}" "${INPUT_FILE}" > "${OUTPUT_FILE}" 2>&1
else
    "${YICES2}" --timeout="${TIMEOUT_SECS}" "${INPUT_FILE}" > "${OUTPUT_FILE}" 2>&1
fi

exit $?
