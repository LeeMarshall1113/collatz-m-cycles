#!/bin/sh
/c/Python314/python ref13.py hard 132 > refchain_hard_132.log 2>&1; echo "hard exit $?"
/c/Python314/python ref13.py shapes 132 > refshapes_132.log 2>&1; echo "shapes 132 exit $?"
/c/Python314/python ref13.py setcmp 132 > setcmp_132.log 2>&1; echo "setcmp exit $?"
