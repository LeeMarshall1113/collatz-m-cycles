import Collatz.TwoRiseCheck
set_option Elab.async false
namespace Collatz.TwoRise.Bench

/-- `n` steps of `c ↦ c · i3 mod 2^W` (the current loop update: a full W×W product). -/
def stepMul (W i3 : Nat) (n : Nat) : Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun c => c)
    (fun _ ih c => ih (Nat.mod (Nat.mul c i3) (Nat.pow 2 W))) n
/-- `n` steps of `c ↦ (c + t 2^W) / 3` (linear time; same value as `c · i3 mod 2^W` for even W). -/
def stepDiv (W : Nat) (n : Nat) : Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun c => c)
    (fun _ ih c => ih (Nat.div (Nat.add c (Nat.mul (Nat.mod (Nat.sub 3 (Nat.mod c 3)) 3) (Nat.pow 2 W))) 3)) n
/-- loop with only the `c` update and a trivial test per step (isolates the loop/let overhead). -/
def loopOnly (W i3 cnt : Nat) : Nat → Nat → Bool :=
  Nat.rec (motive := fun _ => Nat → Nat → Bool) (fun _ _ => true)
    (fun _ ih k c =>
      let c' := Nat.mod (Nat.mul c i3) (Nat.pow 2 W)
      Nat.ble 1 c' && ih (Nat.add k 1) c') cnt
/-- kOK with the pattern search removed. -/
def kNoPat (N B E1 W k0 c : Nat) : Bool :=
  let A := cond (Nat.blt k0 N) (Nat.sub N k0) 1
  let y := Nat.shiftRight c A
  let t := lowScan y W 0
  let D := Nat.pow 2 (Nat.sub (Nat.add B 1) k0)
  Nat.ble k0 (Nat.add B 1) && Nat.beq (Nat.land (Nat.shiftRight y t) 1) 1 &&
    directRange D (Nat.pow 2 A) (Nat.pow 2 W) c (Nat.add t 1) (Nat.pow 2 A)
def loopNoPat (N B E1 W i3 cnt : Nat) : Nat → Nat → Bool :=
  Nat.rec (motive := fun _ => Nat → Nat → Bool) (fun _ _ => true)
    (fun _ ih k c =>
      let c' := Nat.mod (Nat.mul c i3) (Nat.pow 2 W)
      kNoPat N B E1 W k c' && ih (Nat.add k 1) c') cnt


#eval show IO Unit from do let t ← IO.monoMsNow; IO.println s!"T mul32 start {t}"
theorem mul32 : Nat.ble 1 (stepMul 195998 ((2 ^ (195998 + 1) + 1) / 3) 32 1) = true := by
  decide +kernel
#eval show IO Unit from do let t ← IO.monoMsNow; IO.println s!"T mul32 end {t}"

#eval show IO Unit from do let t ← IO.monoMsNow; IO.println s!"T div8 start {t}"
theorem div8 : Nat.ble 1 (stepDiv 195998 8 1) = true := by
  decide +kernel
#eval show IO Unit from do let t ← IO.monoMsNow; IO.println s!"T div8 end {t}"

#eval show IO Unit from do let t ← IO.monoMsNow; IO.println s!"T pow97000 start {t}"
theorem pow97000 : Nat.ble 1 (powMod (2 ^ 195998) 64 ((2 ^ (195998 + 1) + 1) / 3) 97000 1) = true := by
  decide +kernel
#eval show IO Unit from do let t ← IO.monoMsNow; IO.println s!"T pow97000 end {t}"

#eval show IO Unit from do let t ← IO.monoMsNow; IO.println s!"T loopOnly32 start {t}"
theorem loopOnly32 : loopOnly 195998 ((2 ^ (195998 + 1) + 1) / 3) 32 1 1 = true := by
  decide +kernel
#eval show IO Unit from do let t ← IO.monoMsNow; IO.println s!"T loopOnly32 end {t}"

#eval show IO Unit from do let t ← IO.monoMsNow; IO.println s!"T late16 start {t}"
theorem late16 : rangeOK 97951 97965 16 195998 ((2 ^ (195998 + 1) + 1) / 3) 97000 (powMod (2 ^ 195998) 64 ((2 ^ (195998 + 1) + 1) / 3) 96999 1) 16 = true := by
  decide +kernel
#eval show IO Unit from do let t ← IO.monoMsNow; IO.println s!"T late16 end {t}"

#eval show IO Unit from do let t ← IO.monoMsNow; IO.println s!"T r8 start {t}"
theorem r8 : rangeOK 97951 97965 16 195998 ((2 ^ (195998 + 1) + 1) / 3) 101 (powMod (2 ^ 195998) 64 ((2 ^ (195998 + 1) + 1) / 3) 100 1) 8 = true := by
  decide +kernel
#eval show IO Unit from do let t ← IO.monoMsNow; IO.println s!"T r8 end {t}"

#eval show IO Unit from do let t ← IO.monoMsNow; IO.println s!"T r16 start {t}"
theorem r16 : rangeOK 97951 97965 16 195998 ((2 ^ (195998 + 1) + 1) / 3) 101 (powMod (2 ^ 195998) 64 ((2 ^ (195998 + 1) + 1) / 3) 100 1) 16 = true := by
  decide +kernel
#eval show IO Unit from do let t ← IO.monoMsNow; IO.println s!"T r16 end {t}"

#eval show IO Unit from do let t ← IO.monoMsNow; IO.println s!"T r32 start {t}"
theorem r32 : rangeOK 97951 97965 16 195998 ((2 ^ (195998 + 1) + 1) / 3) 101 (powMod (2 ^ 195998) 64 ((2 ^ (195998 + 1) + 1) / 3) 100 1) 32 = true := by
  decide +kernel
#eval show IO Unit from do let t ← IO.monoMsNow; IO.println s!"T r32 end {t}"

#eval show IO Unit from do let t ← IO.monoMsNow; IO.println s!"T mid16 start {t}"
theorem mid16 : rangeOK 97951 97965 16 195998 ((2 ^ (195998 + 1) + 1) / 3) 48801 (powMod (2 ^ 195998) 64 ((2 ^ (195998 + 1) + 1) / 3) 48800 1) 16 = true := by
  decide +kernel
#eval show IO Unit from do let t ← IO.monoMsNow; IO.println s!"T mid16 end {t}"

#eval show IO Unit from do let t ← IO.monoMsNow; IO.println s!"T noPat16 start {t}"
theorem noPat16 : loopNoPat 97951 97965 16 195998 ((2 ^ (195998 + 1) + 1) / 3) 16 101 (powMod (2 ^ 195998) 64 ((2 ^ (195998 + 1) + 1) / 3) 100 1) = true := by
  decide +kernel
#eval show IO Unit from do let t ← IO.monoMsNow; IO.println s!"T noPat16 end {t}"

#eval show IO Unit from do let t ← IO.monoMsNow; IO.println s!"T n37_16 start {t}"
theorem n37_16 : rangeOK 37763 37775 16 75622 ((2 ^ (75622 + 1) + 1) / 3) 101 (powMod (2 ^ 75622) 64 ((2 ^ (75622 + 1) + 1) / 3) 100 1) 16 = true := by
  decide +kernel
#eval show IO Unit from do let t ← IO.monoMsNow; IO.println s!"T n37_16 end {t}"

#eval show IO Unit from do let t ← IO.monoMsNow; IO.println s!"T n60_16 start {t}"
theorem n60_16 : rangeOK 60821 60836 16 121738 ((2 ^ (121738 + 1) + 1) / 3) 101 (powMod (2 ^ 121738) 64 ((2 ^ (121738 + 1) + 1) / 3) 100 1) 16 = true := by
  decide +kernel
#eval show IO Unit from do let t ← IO.monoMsNow; IO.println s!"T n60_16 end {t}"

#eval show IO Unit from do let t ← IO.monoMsNow; IO.println s!"T n152_8 start {t}"
theorem n152_8 : rangeOK 151960 151978 16 304016 ((2 ^ (304016 + 1) + 1) / 3) 101 (powMod (2 ^ 304016) 64 ((2 ^ (304016 + 1) + 1) / 3) 100 1) 8 = true := by
  decide +kernel
#eval show IO Unit from do let t ← IO.monoMsNow; IO.println s!"T n152_8 end {t}"

#eval show IO Unit from do let t ← IO.monoMsNow; IO.println s!"T s6 start {t}"
theorem s6 : rangeOK 97951 97965 16 195998 ((2 ^ (195998 + 1) + 1) / 3) 6 (powMod (2 ^ 195998) 64 ((2 ^ (195998 + 1) + 1) / 3) 5 1) 1 = true := by
  decide +kernel
#eval show IO Unit from do let t ← IO.monoMsNow; IO.println s!"T s6 end {t}"

#eval show IO Unit from do let t ← IO.monoMsNow; IO.println s!"T r61 start {t}"
theorem r61 : rangeOK 97951 97965 16 195998 ((2 ^ (195998 + 1) + 1) / 3) 101 (powMod (2 ^ 195998) 64 ((2 ^ (195998 + 1) + 1) / 3) 100 1) 61 = true := by
  decide +kernel
#eval show IO Unit from do let t ← IO.monoMsNow; IO.println s!"T r61 end {t}"

#eval show IO Unit from do let t ← IO.monoMsNow; IO.println s!"T s5 start {t}"
theorem s5 : rangeOK 97951 97965 16 195998 ((2 ^ (195998 + 1) + 1) / 3) 5 (powMod (2 ^ 195998) 64 ((2 ^ (195998 + 1) + 1) / 3) 4 1) 1 = true := by
  decide +kernel
#eval show IO Unit from do let t ← IO.monoMsNow; IO.println s!"T s5 end {t}"

end Collatz.TwoRise.Bench
