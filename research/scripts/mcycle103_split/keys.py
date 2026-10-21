import pickle, sys
sys.setrecursionlimit(100000)
T = pickle.load(open(sys.argv[1], "rb")); nodes = T['nodes']; R = int(sys.argv[2])
kinds = {}
for n in nodes: kinds[n['kind']] = kinds.get(n['kind'], 0) + 1
print("kinds", kinds)
# keys: root, mid nodes, stop nodes, children of mids, + every R-th node along chains
keys = []  # (idx, type, info)
def seg(i):
    """emit keys for the subtree at i (post-order); return key idx"""
    n = nodes[i]
    if n['kind'] == 'stop':
        keys.append(dict(i=i, t='stop')); return i
    if n['kind'] == 'mid':
        seg(n['ch'][0]); seg(n['ch'][1])
        keys.append(dict(i=i, t='mid', l=n['ch'][0], r=n['ch'][1])); return i
    # chain: follow up to R single steps or until a non-single node
    j, steps = i, 0
    while nodes[j]['kind'] in ('lo', 'hi') and steps < R:
        j = nodes[j]['ch'][0]; steps += 1
    seg(j)
    keys.append(dict(i=i, t='chain', n=steps, to=j)); return i
seg(T['root'])
from collections import Counter
print("R", R, "keys", len(keys), Counter(k['t'] for k in keys), "sum list len", sum(len(nodes[k['i']]['sh']) for k in keys))
pickle.dump(keys, open(sys.argv[3], "wb"))
