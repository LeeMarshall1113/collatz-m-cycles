#!/usr/bin/env bash
# A queue runner for Lean jobs inside ONE broker lease (one Lean process at a time).
# usage (under lease-run.sh): leanq.sh MAX_MIN IDLE_MIN [QUEUE_DIR]
# A job is a file queue/<name>.job with lines: TIMEOUT_S, LOGFILE, then the command (one arg per line).
# Each job runs through run_lean.sh (outer timeout, whole-tree kill); queue/<name>.done marks it finished.
# Stops after MAX_MIN minutes, after IDLE_MIN idle minutes, on queue/STOP, or when the broker asks to yield.
Q=${3:-/c/Users/hackathon/Documents/GitHub/collatz-m-cycles-lean/research/scripts/lean127/queue}
H=/c/Users/hackathon/Documents/GitHub/collatz-m-cycles-lean/research/scripts/lean127
s=$(date +%s); last=$s
while true; do
  now=$(date +%s)
  [ -e "$Q/STOP" ] && { echo "leanq: STOP"; break; }
  [ -n "$BROKER_PREEMPT_FILE" ] && [ -e "$BROKER_PREEMPT_FILE" ] && { echo "leanq: preempted"; break; }
  [ $(( now - s )) -gt $(( $1 * 60 )) ] && { echo "leanq: max time"; break; }
  [ $(( now - last )) -gt $(( $2 * 60 )) ] && { echo "leanq: idle"; break; }
  j=$(ls "$Q"/*.job 2>/dev/null | head -1)
  if [ -z "$j" ]; then sleep 5; continue; fi
  # one Lean process at a time on this machine: wait while any other lean.exe runs
  while tasklist //FI "IMAGENAME eq lean.exe" //NH 2>/dev/null | grep -qi lean.exe; do sleep 30; done
  mapfile -t L < "$j"
  T=${L[0]}; LOG=${L[1]}; CMD=("${L[@]:2}")
  echo "leanq: start $(basename "$j") $(date -u +%H:%MZ)"
  bash "$H/run_lean.sh" "$T" "$LOG" -- "${CMD[@]}"
  mv "$j" "${j%.job}.done"
  if ! tail -1 "$LOG" | grep -q "^RC=0 "; then echo "leanq: FAILED $(basename "$j"), stopping the queue"; break; fi
  echo "leanq: done $(basename "$j") $(date -u +%H:%MZ)"
  last=$(date +%s)
done
