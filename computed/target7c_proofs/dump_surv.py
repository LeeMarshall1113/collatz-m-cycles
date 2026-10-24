"""Dump the survivor list of the repo's fastshapes.surviving(m) (their enumerator) to surv_m<m>.txt,
so that independent code (chain7c.py) can re-check every shape. usage: python dump_surv.py m"""
import sys, os
sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'target7b_push')))
import fastshapes
m = int(sys.argv[1])
Kc, surv = fastshapes.surviving(m, verbose=True)
with open(f'surv_m{m}.txt', 'w') as f:
    f.write(f"# m={m} Kceil={Kc}\n")
    for K, p in surv:
        f.write(f"{K} {p}\n")
print("wrote", len(surv))
