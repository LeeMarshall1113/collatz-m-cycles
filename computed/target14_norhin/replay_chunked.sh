#!/bin/bash
# Resumable leanchecker replay of every built Collatz module, ~20 modules per invocation.
# A chunk is recorded in logs/replay_done.txt only after leanchecker exits 0; rerunning skips done chunks.
# Run under the broker, e.g.:
#   PY=/c/Python314/python LEAN_NUM_THREADS=1 /c/Users/hackathon/.compute-broker/lease-run.sh --detach \
#     --project collatz-lean-rhin --min-gb 7 --want-gb 8 --minutes 1500 --eta-minutes 900 --preemptible \
#     --why "chunked leanchecker replay, 1 thread" --match "leanchecker|lake" -- bash computed/target14_norhin/replay_chunked.sh
cd "$(dirname "$0")/../.."
D=computed/target14_norhin/logs; mkdir -p $D/chunks; touch $D/replay_done.txt
ls Collatz/*.lean | sed 's#/#.#; s#\.lean$##' | sort | while read m; do
  [ -f ".lake/build/lib/lean/$(echo $m | tr . /).olean" ] && echo $m; done > $D/replay_modules.txt
split -l 20 -d -a 3 $D/replay_modules.txt $D/chunks/c_
for f in $D/chunks/c_*; do
  c=$(basename $f)
  grep -qx "$c" $D/replay_done.txt && continue
  t0=$(date -u +%s)
  if lake env leanchecker $(cat $f) > $D/chunks/$c.log 2>&1; then
    echo "$c" >> $D/replay_done.txt; echo "$c ok $(( $(date -u +%s) - t0 ))s" >> $D/replay_progress.txt
  else
    echo "$c FAIL rc=$? $(( $(date -u +%s) - t0 ))s" >> $D/replay_progress.txt
  fi
done
echo "ALL DONE $(wc -l < $D/replay_done.txt) chunks" >> $D/replay_progress.txt
