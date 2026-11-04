#!/bin/bash
# batch 3 (optional): survivor-set comparison at m = 113, 115 and 127
cd /c/Users/hackathon/Documents/GitHub/collatz-m-cycles-release/computed/target11_gapfill
export MPMATH_NOGMPY=1 NUMBA_NUM_THREADS=1 OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1
date -u
/c/Python314/python -u $PWD/setcmp.py 113 115 127 > $PWD/setcmp_113-115-127.log 2>&1; echo "exit $?" >> $PWD/setcmp_113-115-127.log
date -u
