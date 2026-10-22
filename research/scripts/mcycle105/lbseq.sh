#!/usr/bin/env bash
# usage: lbseq.sh TAG MINUTES ETA MOD1 MOD2 ...  -- one lease; `lake build` each module in turn
# (one Lean process at a time); stops at the first failure or when the broker asks to yield.
cd /c/Users/hackathon/Documents/GitHub/collatz-m-cycles-lean
TAG=$1; MIN=$2; ETA=$3; shift 3
LOG=research/scripts/mcycle105/logs/seq_$TAG.log
export LEASE_WAIT=28800 LEASE_CAP_GB=14
cat > research/scripts/mcycle105/logs/seq_$TAG.sh <<EOS
#!/usr/bin/env bash
cd /c/Users/hackathon/Documents/GitHub/collatz-m-cycles-lean
for M in $*; do
  if [ -n "\$BROKER_PREEMPT_FILE" ] && [ -e "\$BROKER_PREEMPT_FILE" ]; then echo "PREEMPTED before \$M"; exit 3; fi
  s=\$(date +%s)
  C:/Users/hackathon/.elan/bin/lake.exe build \$M || { echo "FAILED \$M"; exit 1; }
  echo "DONE \$M \$(( \$(date +%s) - s ))s"
done
EOS
/c/Users/hackathon/.compute-broker/lease-run.sh --project collatz-lean --min-gb 9 --minutes $MIN --eta-minutes $ETA \
  --preemptible --why "Lean m<=105 three-rise: build $TAG" --match "collatz-m-cycles-lean" \
  -- bash research/scripts/mcycle105/logs/seq_$TAG.sh > $LOG 2>&1
echo "rc=$?" >> $LOG
grep -E "DONE|FAILED|PREEMPT|error|rc=" $LOG | tail -40
