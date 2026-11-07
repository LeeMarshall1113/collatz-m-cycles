#!/bin/bash
# Replay every Collatz module's declarations with leanchecker (non-fresh: imports from Mathlib are trusted
# as loaded .oleans; every Collatz declaration, including all decide +kernel certificates, is re-checked).
cd "$(dirname "$0")/../.."
ls Collatz/*.lean | sed 's#/#.#; s#\.lean$##' | sort > computed/target14_norhin/logs/modules.txt
split -n l/4 -d computed/target14_norhin/logs/modules.txt computed/target14_norhin/logs/modbatch_
for f in computed/target14_norhin/logs/modbatch_0*; do
  echo "== batch $f ($(wc -l < $f) modules) start $(date -u +%H:%M:%S)"
  lake env leanchecker $(cat $f) 2>&1 | grep -v "local changes\|packages"
  echo "== batch $f rc=${PIPESTATUS[0]} end $(date -u +%H:%M:%S)"
done
