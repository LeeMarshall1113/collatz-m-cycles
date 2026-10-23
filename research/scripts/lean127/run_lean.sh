#!/usr/bin/env bash
# usage: run_lean.sh TIMEOUT_S LOG -- cmd args...   (run inside a broker lease)
# Runs cmd in the Lean repo, samples peak working set of lean.exe every 15 s, and kills the
# whole process tree (taskkill /T /F) when TIMEOUT_S elapses.
T=$1; LOG=$2; shift 3
cd /c/Users/hackathon/Documents/GitHub/collatz-m-cycles-lean
s=$(date +%s)
"$@" > "$LOG" 2>&1 &
p=$!
wp=$(cat /proc/$p/winpid 2>/dev/null)
peak=0
while kill -0 $p 2>/dev/null; do
  sleep 5
  m=$(tasklist //FI "IMAGENAME eq lean.exe" //FO CSV //NH 2>/dev/null | awk -F'","' '{gsub(/[^0-9]/,"",$5); s+=$5} END{print s+0}')
  [ "$m" -gt "$peak" ] && peak=$m
  if [ $(( $(date +%s) - s )) -gt "$T" ]; then
    echo "TIMEOUT after ${T}s: killing tree $wp" | tee -a "$LOG"
    taskkill //T //F //PID $wp >/dev/null 2>&1
    sleep 5; break
  fi
done
wait $p; rc=$?
echo "RC=$rc wall=$(( $(date +%s) - s ))s peak_lean_ws_KB=$peak" | tee -a "$LOG"
