#!/bin/sh
/c/Python314/python ref13.py hard 133 > refchain_hard_133.log 2>&1; echo "hard exit $?"
/c/Python314/python ref13.py shapes 133 > refshapes_133.log 2>&1; echo "shapes 133 exit $?"
/c/Python314/python ref13.py setcmp 133 > setcmp_133.log 2>&1; echo "setcmp exit $?"
