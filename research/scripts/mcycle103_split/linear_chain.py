"""Replace the nested `.trans` term of `allPairsN` (maxRecDepth for many chunks) by a linear chain
of named lemmas rcN_j : RangeCond N B 1 hi_j. Chunk bounds are read from the tr lines."""
import re, sys
path = sys.argv[1]
src = open(path, encoding="utf-8").read()
pat = re.compile(r"theorem (tr(\d+)_(\d+)) : rangeOK (\d+) (\d+) \d+ \d+ \(\(2 \^ \(\d+ \+ 1\) \+ 1\) / 3\) (\d+) .* (\d+) = true")
trs = pat.findall(src)
assert trs, "no chunks"
N = trs[0][1]; B = trs[0][4]
out = []
hi_prev = None
for name, n, j, N_, B_, k, cnt in trs:
    assert N_ == N and B_ == B
    k, cnt = int(k), int(cnt)
    if hi_prev is None:
        assert k == 1
        out.append(f"theorem rc{N}_{j} : RangeCond {N} {B} 1 {k + cnt} := rangeOK_sound {name}\n")
    else:
        assert k == hi_prev
        out.append(f"theorem rc{N}_{j} : RangeCond {N} {B} 1 {k + cnt} :=\n  (rc{N}_{int(j) - 1}).trans (rangeOK_sound {name})\n")
    hi_prev = k + cnt
assert hi_prev == int(N) + 1
last = trs[-1][2]
m = re.search(rf"theorem allPairs{N} : AllPairs {N} {B} := allPairs_of_range [^\n]*\n", src)
assert m
new = "\n".join(out) + f"\ntheorem allPairs{N} : AllPairs {N} {B} := allPairs_of_range rc{N}_{last}\n"
src = src[:m.start()] + new + src[m.end():]
open(path, "w", encoding="utf-8", newline="").write(src)
print(N, B, len(trs), "chunks")
