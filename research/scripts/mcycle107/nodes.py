import sys, os, time, threading
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'mcycle105'))
import memguard; memguard.start(3.0e9)
a = sys.argv[1:]; sys.argv = [sys.argv[0]]
threading.stack_size(250 * 2 ** 20)
import chain3 as C
sys.setrecursionlimit(2000000)
def main():
    for m in map(int, a):
        t = time.time(); P = C.L.plan_m(m, need_ns=False)
        print(m, "nodes", P['nodes'], "shapes", len(P['certs']), "small", sum(c['small'] for c in P['certs']),
              "%.0fs" % (time.time() - t), flush=True)
th = threading.Thread(target=main); th.start(); th.join()
