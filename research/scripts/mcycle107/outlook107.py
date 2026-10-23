"""Which B3 points does each m in 106..M need (B2 grid fixed = grid103)?  Cost = sum N^3 over points
not yet kernel-checked.  usage: python outlook107.py m1 m2 [cap]"""
import sys, os, time, pickle
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'mcycle105'))
a = sys.argv[1:]; sys.argv = [sys.argv[0]]
import chain3 as C
import threading, ctypes
from ctypes import wintypes
sys.setrecursionlimit(2000000); threading.stack_size(250 * 2 ** 20)


class _PMC(ctypes.Structure):
    _fields_ = [("cb", wintypes.DWORD), ("PageFaultCount", wintypes.DWORD)] + \
               [(n, ctypes.c_size_t) for n in ("PeakWorkingSetSize", "WorkingSetSize", "QuotaPeakPagedPoolUsage",
                                               "QuotaPagedPoolUsage", "QuotaPeakNonPagedPoolUsage",
                                               "QuotaNonPagedPoolUsage", "PagefileUsage", "PeakPagefileUsage")]


def _guard(limit=2.5e9):
    """memory bound for this unleased helper: exit if commit (PagefileUsage) exceeds 2.5 GB"""
    k32 = ctypes.WinDLL('kernel32'); ps = ctypes.WinDLL('psapi')
    k32.GetCurrentProcess.restype = wintypes.HANDLE
    ps.GetProcessMemoryInfo.argtypes = [wintypes.HANDLE, ctypes.c_void_p, wintypes.DWORD]
    h = k32.GetCurrentProcess(); pmc = _PMC(); pmc.cb = ctypes.sizeof(_PMC)
    while True:
        ps.GetProcessMemoryInfo(h, ctypes.byref(pmc), pmc.cb)
        if pmc.PagefileUsage > limit:
            print("MEMORY GUARD: commit > 2.5 GB, exiting", flush=True); os._exit(9)
        time.sleep(0.3)


threading.Thread(target=_guard, daemon=True).start()
m1, m2 = int(a[0]), int(a[1]); cap = int(a[2]) if len(a) > 2 else 1200
g2 = C.grid103(); b3 = dict(C.b3_all())
built = set(int(x) for x in os.environ.get('BUILT', '79,122,203,325').split(','))
cand = [N for N in sorted(b3) if N <= cap]
def g3of(S): return sorted((N, b3[N]) for N in S)
def cost(S): return sum(N ** 3 for N in S if N not in built)
def main():
  global built
  for m in range(m1, m2 + 1):
      t = time.time()
      try:
          P = C.L.plan_m(m, need_ns=False)
      except Exception as e:
          print(m, "plan failed", repr(e)[:200], flush=True); continue
      certs = P['certs']
      # hardest first
      def ok(S, first=[None]):
          g3 = g3of(S)
          if first[0] is not None and not C.shape_ok3(m, g2, g3, first[0])[0]:
              return False
          for c in certs:
              if not C.shape_ok3(m, g2, g3, c)[0]:
                  first[0] = c; return False
          return True
      S = set(cand)
      if not ok(S):
          print(m, "nodes", P['nodes'], "shapes", len(certs), "FAILS even with all B3 <=", cap, flush=True); continue
      used = set()
      for c in certs: C.shape_ok3(m, g2, g3of(S), c, used)
      S = {N for N, _ in used}
      changed = True
      while changed:
          changed = False
          for N in sorted(S, key=lambda N: -(0 if N in built else N ** 3)):
              if ok(S - {N}): S = S - {N}; changed = True
          # swap: replace one point by a cheaper (smaller N or built) point
          for N in sorted(S, key=lambda N: -(0 if N in built else N ** 3)):
              for M in sorted(cand, key=lambda M: 0 if M in built else M ** 3):
                  T = (S - {N}) | {M}
                  if cost(T) < cost(S) and ok(T): S = T; changed = True; break
      print(m, "nodes", P['nodes'], "shapes", len(certs), "B3", sorted(S), "new", sorted(N for N in S if N not in built),
            "newcost(M triples)~%.1f" % (cost(S) / 6e6), "%.0fs" % (time.time() - t), flush=True)
      built |= S

t_ = threading.Thread(target=main); t_.start(); t_.join()