import sys, os, pickle
from fractions import Fraction as F
G = sys.argv[1]; sys.path.insert(0, G)
sys.setrecursionlimit(100000)
import gen_lean as L, gen_mcycle as M
P = L.plan_m(103, need_ns=False)
st = [(e[0],) + (0,) * 5 + (e[6],) for e in P['st']] + [(P['Ks'],) + (0,) * 5 + (P['stall'][5],)]
Kc, Km = P['Kceil'], P['Ks']
nodes = []   # (fuel, a,b,c,d, kind, children idx, mults list, size, shapes)
def build(fuel, a, b, c, d):
    i = len(nodes); nodes.append(None)
    f, e = b + d, a + c
    if fuel == 0: raise Exception("fuel")
    if Kc <= f:
        nodes[i] = dict(fuel=fuel, abcd=(a,b,c,d), kind='stop', ch=[], mu=[], size=1, sh=[]); return i
    ep = M.eps_at(max(f, Km), st)
    assert ep is not None
    if F(e, f) <= M.DLO:
        j = build(fuel - 1, e, f, c, d); kind = 'lo'; ch = [j]; mu = []
    elif M.DHI + ep <= F(e, f):
        j = build(fuel - 1, a, b, e, f); kind = 'hi'; ch = [j]; mu = []
    else:
        mu = M.mults(st, Kc, Km, e, f)
        j1 = build(fuel - 1, a, b, e, f); j2 = build(fuel - 1, e, f, c, d); kind = 'mid'; ch = [j1, j2]
    size = 1 + sum(nodes[j]['size'] for j in ch)
    sh = mu + sum((nodes[j]['sh'] for j in ch), [])
    nodes[i] = dict(fuel=fuel, abcd=(a,b,c,d), kind=kind, ch=ch, mu=mu, size=size, sh=sh)
    return i
a, b, c, d = P['abcd']
r = build(P['fuel'], a, b, c, d)
print("total nodes", nodes[r]['size'], "shapes", len(nodes[r]['sh']), "maxdepth", P['fuel'] - min(n['fuel'] for n in nodes))
for S in (500, 1000, 2000, 3000, 4000, 6000):
    exp, front = 0, []
    stack = [r]
    while stack:
        i = stack.pop()
        if nodes[i]['size'] > S: exp += 1; stack += nodes[i]['ch']
        else: front.append(i)
    print("S", S, "expanded", exp, "frontier", len(front), "max frontier size", max(nodes[i]['size'] for i in front))
pickle.dump(dict(nodes=nodes, root=r, P=P, Kc=Kc, Km=Km), open(sys.argv[2], "wb"))
