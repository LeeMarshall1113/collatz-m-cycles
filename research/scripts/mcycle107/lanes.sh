#!/usr/bin/env bash
# usage (inside ONE lease sized for two Lean processes): lanes.sh "LANE_A targets" "LANE_B targets" "JOIN targets..."
# Runs lane A and lane B side by side (each `lake build` one target at a time -> at most two Lean
# processes), then each JOIN group (space-separated targets within a group built by one lake call;
# groups separated by ';'). Checks the broker preempt file between targets.
cd /c/Users/hackathon/Documents/GitHub/collatz-m-cycles-lean
LAKE=C:/Users/hackathon/.elan/bin/lake.exe
lane() {
  for M in $2; do
    if [ -n "$BROKER_PREEMPT_FILE" ] && [ -e "$BROKER_PREEMPT_FILE" ]; then echo "[$1] PREEMPTED before $M"; return 3; fi
    s=$(date +%s)
    $LAKE build $M > research/scripts/mcycle107/logs/lane_$1_${M##*.}.log 2>&1 || { echo "[$1] FAILED $M"; tail -30 research/scripts/mcycle107/logs/lane_$1_${M##*.}.log; return 1; }
    echo "[$1] DONE $M $(( $(date +%s) - s ))s $(date -u +%H:%MZ)"
  done
}
lane A "$1" & pa=$!
lane B "$2" & pb=$!
wait $pa; ra=$?; wait $pb; rb=$?
[ $ra -eq 0 ] && [ $rb -eq 0 ] || { echo "LANES FAILED ra=$ra rb=$rb"; exit 1; }
IFS=';' read -ra JGRPS <<< "$3"
for g in "${JGRPS[@]}"; do
  [ -z "${g// }" ] && continue
  if [ -n "$BROKER_PREEMPT_FILE" ] && [ -e "$BROKER_PREEMPT_FILE" ]; then echo "PREEMPTED before $g"; exit 3; fi
  s=$(date +%s)
  $LAKE build $g || { echo "FAILED $g"; exit 1; }
  echo "DONE $g $(( $(date +%s) - s ))s $(date -u +%H:%MZ)"
done
s=$(date +%s); $LAKE env lean scripts/Statement.lean; echo "STATEMENT rc=$? $(( $(date +%s) - s ))s"
s=$(date +%s); $LAKE env lean scripts/AxiomAudit.lean; echo "AUDIT rc=$? $(( $(date +%s) - s ))s"
