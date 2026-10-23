import os, time, ctypes, threading
from ctypes import wintypes


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
            print("MEMORY GUARD: commit > %.1f GB, exiting" % (limit / 1e9), flush=True); os._exit(9)
        time.sleep(0.3)


def start(limit=2.5e9):
    threading.Thread(target=_guard, args=(limit,), daemon=True).start()
