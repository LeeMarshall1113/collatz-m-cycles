#!/usr/bin/env bash
cd /c/Users/hackathon/Documents/GitHub/collatz-m-cycles-lean
B="Collatz.MCycle108Def $(for i in $(seq 1 57); do printf 'Collatz.MCycle108Walk%d ' $i; done) Collatz.MCycle108Shapes"
bash research/scripts/mcycle109/lanes.sh "Collatz.MCycleTwoRise108" "$B" "Collatz.MCycleGrid108;Collatz.MCycle108"
