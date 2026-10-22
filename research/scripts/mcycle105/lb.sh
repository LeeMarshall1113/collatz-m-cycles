#!/usr/bin/env bash
# usage: lb.sh MODULE MINUTES ETA  -- one leased `lake build MODULE` (one Lean process at a time)
cd /c/Users/hackathon/Documents/GitHub/collatz-m-cycles-lean
M=$1; MIN=${2:-60}; ETA=${3:-20}
LOG=research/scripts/mcycle105/logs/$M.log
export LEASE_WAIT=28800 LEASE_CAP_GB=14
start=$(date +%s)
/c/Users/hackathon/.compute-broker/lease-run.sh --project collatz-lean --min-gb 9 --minutes $MIN --eta-minutes $ETA \
  --preemptible --why "Lean m<=105 three-rise: build $M" --match "collatz-m-cycles-lean" \
  -- C:/Users/hackathon/.elan/bin/lake.exe build $M > $LOG 2>&1
rc=$?
echo "rc=$rc secs=$(( $(date +%s) - start ))" >> $LOG
tail -40 $LOG
