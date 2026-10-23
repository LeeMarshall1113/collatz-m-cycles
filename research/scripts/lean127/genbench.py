import sys
def W(N):
    w=2*N+2*16+64; return w+(w%2)
def stamp(tag):
    return f'#eval show IO Unit from do let t ← IO.monoMsNow; IO.println s!"T {tag} {{t}}"\n'
def thm(name,N,B,k,cnt):
    w=W(N); i3=f"((2 ^ ({w} + 1) + 1) / 3)"
    c0="1" if k==1 else f"(powMod (2 ^ {w}) 64 {i3} {k-1} 1)"
    return (stamp(name+" start")+f"theorem {name} : rangeOK {N} {B} 16 {w} {i3} {k} {c0} {cnt} = true := by\n  decide +kernel\n"+stamp(name+" end")+"\n")
def write(fn, items):
    s="import Collatz.TwoRiseCheck\nset_option Elab.async false\nnamespace Collatz.TwoRise\n\n"
    for it in items: s+=thm(*it)
    s+="end Collatz.TwoRise\n"
    open(fn,"w",encoding="utf-8").write(s)
if __name__=="__main__":
    write("Bench1.lean",[("a8",97951,97965,1,8),("a16",97951,97965,1,16),("a32",97951,97965,1,32),("a61",97951,97965,1,61),
                   ("mid16",97951,97965,48801,16),("late16",97951,97965,97000,16),
                   ("n60_16",60821,60836,1,16),("n37_16",37763,37775,1,16)])
