"""b3join.b3_exact with an explicit partition count s (a performance parameter only: the P list is split by the top
s bits of its bit-reversed key, every partition is joined against the full Q side; b3_join asserts s <= t + 1).
For N >= 65000 b3join uses its unpacked path and picks s so that a part has <= 25e6 keys (s = 8 at N = 90,000:
256 parts, each re-enumerating Q, ~92 s per part).  s = 6 gives 64 parts of ~63e6 keys (~2.5 GB).
Same retry rule and literal witness re-simulation as b3_exact.  usage: python b3drive.py N s"""
import sys, os, math
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'target7b_push'))
import b3join as J     # noqa: E402

if __name__ == "__main__":
    N, s = int(sys.argv[1]), int(sys.argv[2])
    t = max(0, int(2 * math.log2(N)) - 7)
    Kmax = J.b2_of(N)
    print(f"N={N} Kmax=B2(N)={Kmax} t={t} s={s}", flush=True)
    U, c = J.pack_rows(N, Kmax)
    while True:
        r = J.b3_join(N, t, Kmax=Kmax, s=s, verbose=True, U=U, c=c)
        if r['exact']:
            break
        t -= 3
    nbits, ks = J.B3M.witness(r['arg'], N)
    assert sum(ks) == r['B3'] and nbits <= N, (ks, r)
    r['witness_ks'] = ks
    r.pop('found')
    print(r, flush=True)
