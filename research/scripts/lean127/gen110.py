"""m = 110 data via mcycle109/gen109.py, with the B2 points of target12 PLAN §2.1 (grid110 = grid109 ++ these)."""
import os, sys, runpy
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'mcycle109'))
import gen109 as G
G.B2NEW[110] = G.B2NEW[109] + [(247533, 247549), (384012, 384028), (403213, 403231), (647476, 647493)]
if __name__ == "__main__":
    import threading
    sys.argv = [sys.argv[0], os.path.join(HERE, '..', '..', '..', 'Collatz'), '110']
    sys.setrecursionlimit(3000000); threading.stack_size(250 * 2 ** 20)
    th = threading.Thread(target=G._main); th.start(); th.join()
