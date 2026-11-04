#!/bin/bash
# batch 1: fastchain (serial, 72-pt refereed B4 grid) at the gap m, then 125, 126 with the same grid
cd /c/Users/hackathon/Documents/GitHub/collatz-m-cycles-release/computed/target11_gapfill
export MPMATH_NOGMPY=1 NUMBA_NUM_THREADS=1 OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1
P=/c/Python314/python
D=/c/Users/hackathon/Documents/GitHub/collatz-m-cycles-release/computed/target11_gapfill
date -u
$P -u $D/fc_gap.py 112,113,115,122,123,124 > $D/fc_gap_112-124.log 2>&1; echo "exit $?" >> $D/fc_gap_112-124.log
date -u
$P -u $D/fc_gap.py 125,126 > $D/fc_gap_125-126.log 2>&1; echo "exit $?" >> $D/fc_gap_125-126.log
date -u
