#!/bin/bash
# batch 2: referee (refshapes count + refchain screen) at m = 122..126, then the survivor-set comparison
cd /c/Users/hackathon/Documents/GitHub/collatz-m-cycles-release/computed/target11_gapfill
export MPMATH_NOGMPY=1 NUMBA_NUM_THREADS=1 OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1
P=/c/Python314/python
D=$PWD
date -u
for m in 122 123 124 125 126; do
  $P -u $D/ref_gap.py $m > $D/refshapes_$m.log 2>&1; echo "exit $?" >> $D/refshapes_$m.log; date -u
done
$P -u $D/setcmp.py 112 122 123 124 125 126 > $D/setcmp_112-126.log 2>&1; echo "exit $?" >> $D/setcmp_112-126.log
date -u
