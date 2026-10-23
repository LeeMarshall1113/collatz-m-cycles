import Collatz.ThreeRiseSplit

/-!
# Kernel timing probes (not part of the proof; not imported by `Collatz`)

Build alone with `lake build Collatz.BenchKernel`; `profiler` prints the kernel time per declaration.

* `b2_*`: `TwoRise.rangeOK` at `N = 60821` (`AllPairs 60821 60836`, 63 min in branch m103) for 20 first
  rises, against the same loop with the inverse update `c ↦ c / 3 mod 2^W` done as an exact division
  (`(c + j 2^W) / 3`) instead of a full multiplication and a division by `2^W`, and the update alone.
* `b3_*`: `rangeOK3` / `lRangeOK3` at `N = 325` for a known number of triples.
* `join_*`: the packed-field join step of the proposed certificate checker (one `(k₀, ℓ₀)` against all
  `(K, ℓ₁)` fields at once: an add, a multiply by a small number, two ands and a compare on numbers of
  `65 F` bits), for `F` = 52 000 (about `N = 325`) and 357 000 (about `N = 845`) fields.
-/

set_option Elab.async false
set_option profiler true
set_option profiler.threshold 1

namespace Collatz.Bench

open Collatz.TwoRise Collatz.ThreeRise

/-- `c / 3 mod 2^W` for `c < 2^W`: `(c + j 2^W) / 3` with `j ≡ −c 2^W (mod 3)`. -/
def div3 (W2 c : Nat) : Nat :=
  Nat.div (Nat.add c (Nat.mul (Nat.mod (Nat.sub 3 (Nat.mod (Nat.mul (Nat.mod c 3) (Nat.mod W2 3)) 3)) 3) W2)) 3

def loopX (N B E1 W cnt : Nat) : Nat → Nat → Bool :=
  Nat.rec (motive := fun _ => Nat → Nat → Bool) (fun _ _ => true)
    (fun _ ih k c =>
      let c' := div3 (Nat.pow 2 W) c
      kOK N B E1 W k c' && ih (Nat.add k 1) c') cnt

def updOnly (W i3 cnt : Nat) : Nat → Bool :=
  Nat.rec (motive := fun _ => Nat → Bool) (fun c => Nat.blt 0 c)
    (fun _ ih c => ih (Nat.mod (Nat.mul c i3) (Nat.pow 2 W))) cnt

def updOnlyX (W cnt : Nat) : Nat → Bool :=
  Nat.rec (motive := fun _ => Nat → Bool) (fun c => Nat.blt 0 c)
    (fun _ ih c => ih (div3 (Nat.pow 2 W) c)) cnt

theorem b2_rangeOK : rangeOK 60821 60836 16 121738 ((2 ^ (121738 + 1) + 1) / 3) 1 1 20 = true := by
  decide +kernel

-- `loopX 60821 60836 16 121738 20 1 1 = true` took 372 s against 39.8 s for `b2_rangeOK`: the
-- exact division is not a win, so it is not re-run.

theorem b2_upd : updOnly 121738 ((2 ^ (121738 + 1) + 1) / 3) 20 1 = true := by
  decide +kernel

theorem b2_updX : updOnlyX 121738 20 1 = true := by
  decide +kernel

/-- `rangeOK3 325 340` for `k₀ = 250 .. 259`: 25 239 triples (mirror count). -/
theorem b3_range : rangeOK3 325 340 16 776 ((2 ^ (776 + 1) + 1) / 3) 250
    (TwoRise.powMod (2 ^ 776) 64 ((2 ^ (776 + 1) + 1) / 3) 249 1) 10 = true := by
  decide +kernel

/-- One packed-field join step (see the module doc). -/
def joinStep (T MASK G P : Nat) (ONES : Nat) : Bool :=
  Nat.beq (Nat.land (Nat.add (Nat.land (Nat.add T (Nat.mul P ONES)) MASK) MASK) G) G

def joinLoop (T MASK G ONES : Nat) : Nat → Nat → Bool :=
  Nat.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun _ ih P => joinStep T MASK G P ONES && ih (Nat.mod (Nat.add (Nat.mul P 6364136223846793005) 1442695040888963407) (2 ^ 63)))

/-- `F` fields of 65 bits: `ONES = Σ 2^{65 i}`, `MASK = (2^64 − 1) ONES`, `G = 2^64 ONES`, `T` a
pseudo-random `MASK`-masked number. -/
def joinRun (F n : Nat) : Bool :=
  let ONES := Nat.div (Nat.sub (Nat.pow 2 (Nat.mul 65 F)) 1) (Nat.sub (Nat.pow 2 65) 1)
  let MASK := Nat.mul (Nat.sub (Nat.pow 2 64) 1) ONES
  let G := Nat.mul (Nat.pow 2 64) ONES
  let T := Nat.land (Nat.pow 3 (Nat.mul 41 F)) MASK
  joinLoop T MASK G ONES n 12345

theorem join_setup_52k : joinRun 52000 0 = true := by
  decide +kernel

theorem join_52k_x100 : joinRun 52000 100 = true := by
  decide +kernel

theorem join_setup_357k : joinRun 357000 0 = true := by
  decide +kernel

theorem join_357k_x50 : joinRun 357000 50 = true := by
  decide +kernel

end Collatz.Bench
