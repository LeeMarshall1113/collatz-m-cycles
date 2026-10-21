import Collatz.MCycleWalk

/-!
# Evaluating the Farey walk in pieces

`decide +kernel` on a whole `mOK` evaluates `walk` in one kernel check, whose memory grows with the
walk (about 15 GB for the 13 126 nodes of `m = 102`, over 18 GB for `m = 103`). The lemmas here
rewrite `walk` node by node without evaluating it, so that a data module can prove
`D.shapes = L` from many small kernel checks:

* `walk_stop`: at a node past the ceiling the walk is empty;
* `walk_wchain`: along a run of nodes where the mediant leaves the window on one side, the walk at
  the start of the run equals the walk at its end (`wchain`, `n` steps, fuel decreases by `n`);
* `walk_mid`: at a node whose mediant is in the window, the walk is the multiples followed by the
  two subwalks;
* `certsOK_append`: the certificate check of the listed shapes, in pieces.

Nothing here changes `walk`, `mOK` or their soundness proofs; it only computes the same value.
-/

namespace Collatz

/-- One single-child step of `walk` (`none` if the node stops, fails or splits). -/
def wstep (st : List (ℕ × ℚ)) (Kc Km a b c d : ℕ) : Option (ℕ × ℕ × ℕ × ℕ) :=
  if Kc ≤ b + d then none
  else match epsAt (max (b + d) Km) st with
    | none => none
    | some ε =>
      if ((a + c : ℕ) : ℚ) / ((b + d : ℕ) : ℚ) ≤ deltaLo then some (a + c, b + d, c, d)
      else if deltaHi + ε ≤ ((a + c : ℕ) : ℚ) / ((b + d : ℕ) : ℚ) then some (a, b, a + c, b + d)
      else none

/-- `n` single-child steps of `walk`. -/
def wchain (st : List (ℕ × ℚ)) (Kc Km : ℕ) : ℕ → ℕ → ℕ → ℕ → ℕ → Option (ℕ × ℕ × ℕ × ℕ)
  | 0, a, b, c, d => some (a, b, c, d)
  | n + 1, a, b, c, d =>
    match wstep st Kc Km a b c d with
    | some (a', b', c', d') => wchain st Kc Km n a' b' c' d'
    | none => none

/-- The node splits: `wmid` checks the conditions of the last branch of `walk`. -/
def wmid (st : List (ℕ × ℚ)) (Kc Km a b c d : ℕ) : Bool :=
  !(decide (Kc ≤ b + d)) &&
    match epsAt (max (b + d) Km) st with
    | none => false
    | some ε =>
      !(decide (((a + c : ℕ) : ℚ) / ((b + d : ℕ) : ℚ) ≤ deltaLo)) &&
        !(decide (deltaHi + ε ≤ ((a + c : ℕ) : ℚ) / ((b + d : ℕ) : ℚ)))

theorem walk_stop {st : List (ℕ × ℚ)} {Kc Km : ℕ} (f : ℕ) {a b c d : ℕ} (h : Kc ≤ b + d) :
    walk st Kc Km (f + 1) a b c d = [] := by
  simp only [walk, h, if_true]

theorem walk_wstep {st : List (ℕ × ℚ)} {Kc Km : ℕ} (f : ℕ) {a b c d a' b' c' d' : ℕ}
    (h : wstep st Kc Km a b c d = some (a', b', c', d')) :
    walk st Kc Km (f + 1) a b c d = walk st Kc Km f a' b' c' d' := by
  unfold wstep at h
  rw [walk]
  by_cases h1 : Kc ≤ b + d
  · simp [h1] at h
  · rw [if_neg h1] at h ⊢
    cases he : epsAt (max (b + d) Km) st with
    | none => rw [he] at h; simp at h
    | some ε =>
      rw [he] at h
      simp only at h ⊢
      by_cases h3 : ((a + c : ℕ) : ℚ) / ((b + d : ℕ) : ℚ) ≤ deltaLo
      · rw [if_pos h3] at h ⊢
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl, rfl⟩ := h
        rfl
      · rw [if_neg h3] at h ⊢
        by_cases h4 : deltaHi + ε ≤ ((a + c : ℕ) : ℚ) / ((b + d : ℕ) : ℚ)
        · rw [if_pos h4] at h ⊢
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl, rfl⟩ := h
          rfl
        · rw [if_neg h4] at h
          simp at h

theorem walk_wchain {st : List (ℕ × ℚ)} {Kc Km : ℕ} (f : ℕ) : ∀ (n : ℕ) {a b c d a' b' c' d' : ℕ},
    wchain st Kc Km n a b c d = some (a', b', c', d') →
    walk st Kc Km (f + n) a b c d = walk st Kc Km f a' b' c' d'
  | 0, a, b, c, d, a', b', c', d', h => by
    simp only [wchain, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl, rfl⟩ := h
    rfl
  | n + 1, a, b, c, d, a', b', c', d', h => by
    simp only [wchain] at h
    cases hs : wstep st Kc Km a b c d with
    | none => rw [hs] at h; simp at h
    | some q =>
      obtain ⟨a₁, b₁, c₁, d₁⟩ := q
      rw [hs] at h
      rw [show f + (n + 1) = (f + n) + 1 by omega, walk_wstep (f + n) hs]
      exact walk_wchain f n h

theorem walk_mid {st : List (ℕ × ℚ)} {Kc Km : ℕ} (f : ℕ) {a b c d e g : ℕ}
    (h : wmid st Kc Km a b c d = true) (he : a + c = e) (hg : b + d = g) :
    walk st Kc Km (f + 1) a b c d =
      mults st Kc Km e g (Kc / g + 1) 1 ++ (walk st Kc Km f a b e g ++ walk st Kc Km f e g c d) := by
  subst he hg
  unfold wmid at h
  rw [walk]
  by_cases h1 : Kc ≤ b + d
  · simp [h1] at h
  · rw [if_neg h1]
    simp only [h1, decide_false, Bool.not_false, Bool.true_and] at h
    cases he : epsAt (max (b + d) Km) st with
    | none => rw [he] at h; simp at h
    | some ε =>
      rw [he] at h
      simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at h
      obtain ⟨h3, h4⟩ := h
      simp only
      rw [if_neg h3, if_neg h4]

theorem certsOK_append (m S : ℕ) (grid : List (ℕ × ℕ)) (certs : List ShapeCert)
    (l₁ l₂ : List (ℕ × ℕ)) :
    certsOK m S grid certs (l₁ ++ l₂) = (certsOK m S grid certs l₁ && certsOK m S grid certs l₂) := by
  simp only [certsOK, List.all_append]

end Collatz
