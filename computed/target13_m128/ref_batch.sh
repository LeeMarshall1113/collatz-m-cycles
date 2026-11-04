#!/bin/sh
# referee survivor count + own chain screen, then set comparison, m = 128..131 (sequential, 1 thread)
for m in 128 129 130 131; do /c/Python314/python ref13.py shapes $m > refshapes_$m.log 2>&1; echo "shapes $m exit $?"; done
/c/Python314/python ref13.py setcmp 128 129 130 131 > setcmp_128-131.log 2>&1; echo "setcmp exit $?"
