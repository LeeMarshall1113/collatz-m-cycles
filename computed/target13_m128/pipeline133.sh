#!/bin/sh
# wait for the B2 batch, record points, then chain m=133 and the referee batch, each under its own lease
D=/c/Users/hackathon/Documents/GitHub/collatz-m-cycles-release-t13/computed/target13_m128; cd $D
until grep -q "lease-run: released" b2_133.log; do sleep 120; done
grep -q "N=5888465 B2=" b2_133.log || { echo "B2 batch incomplete"; exit 1; }
/c/Python314/python - <<'PY'
import json,re
d=json.load(open('b2_new_g13.json'))
for l in open('b2_133.log'):
    m=re.match(r"N=(\d+) B2=(\d+) .*arg=\('pair', (\d+), (\d+), (\d+)\).* ([\d.]+)s",l)
    if m:
        N,B=int(m[1]),int(m[2])
        d[str(N)]={"N":N,"B2":B,"exc":B-N,"arg":["pair",int(m[3]),int(m[4]),int(m[5])],"secs":float(m[6]),"src":"b2fast local (b2_133.log)","referee":f"myb2 on Modal (modal_logs/ref_b2_{N}.log)"}
json.dump(d,open('b2_new_g13.json','w'),indent=1)
PY
export PY=/c/Python314/python MPMATH_NOGMPY=1 NUMBA_NUM_THREADS=1 OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1
/c/Users/hackathon/.compute-broker/lease-run.sh --project collatz-m128 --min-gb 1 --minutes 600 --eta-minutes 300 --why "all-shapes chain m=133 (1 process)" --match "fastchain13\.py" -- /c/Python314/python fastchain13.py 133 > chain_133.out 2>&1
/c/Users/hackathon/.compute-broker/lease-run.sh --project collatz-m128 --min-gb 2 --minutes 300 --eta-minutes 110 --why "referee refchain/refshapes/setcmp m=133 (1 thread)" --match "ref13\.py" -- sh ref_batch133.sh > ref_batch133_lease.log 2>&1
echo PIPELINE DONE
