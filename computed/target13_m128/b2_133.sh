#!/bin/sh
# exact B2 points for m = 133, smallest first, one process per point; stops at a point boundary if preempted
cd ../target7b_push
for N in 142591 227256 360191 579108 1478908 2344024 3715201 5888465; do
  if [ -n "${BROKER_PREEMPT_FILE:-}" ] && [ -f "$BROKER_PREEMPT_FILE" ]; then echo "PREEMPTED before N=$N"; exit 10; fi
  /c/Python314/python b2fast.py $N; echo "N=$N exit $?"
done
