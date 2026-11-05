import Mathlib

/-!
# Generic analytic lemmas for the Gelfond method

* L4 `hermite`: Hermite interpolation at the integer nodes `0, …, h−1` with multiplicity `M`, with a
  growth bound from Newton's divided differences: every divided difference is at most `2^k ε`
  because distinct nodes are at distance at least 1.
* L5 `schwarz`: if an entire `g` has zeros of order `M` at `0, …, h−1`, then on `|z| ≤ R`
  we have `|g(z)| ≤ S · Π |z − l|^M / (R − h)^{hM}`. The function `g / Π (z − l)^M` is entire, so
  the maximum modulus principle applies.

The removable-singularity part of L5 may be ported from M. Karatarakis and F. Wiedijk, *A
formalization of the Gelfond–Schneider theorem* (arXiv 2603.24823); credit to be recorded here when
it is.
-/

namespace Collatz.Gelfond

open Finset Complex

/-- **L4.** Hermite interpolation with a growth bound. -/
theorem hermite (h M : ℕ) (D : ℕ → ℕ → ℂ) {ε : ℝ} (hD : ∀ l < h, ∀ m < M, ‖D l m‖ ≤ ε)
    (hε : 0 ≤ ε) :
    ∃ P : Polynomial ℂ, (∀ l < h, ∀ m < M, (Polynomial.derivative^[m] P).eval (l : ℂ) = D l m) ∧
      ∀ z : ℂ, ‖P.eval z‖ ≤ ε * (h * M) * (2 * (‖z‖ + h)) ^ (h * M) := by
  sorry

/-- **L5.** The Schwarz-type bound for an entire function with zeros of order `M` at `0..h−1`. -/
theorem schwarz {g : ℂ → ℂ} (hg : Differentiable ℂ g) (h M : ℕ)
    (hz : ∀ l < h, ∀ m < M, iteratedDeriv m g (l : ℂ) = 0) {R S : ℝ} (hR : (h : ℝ) < R)
    (hS : ∀ ζ : ℂ, ‖ζ‖ = R → ‖g ζ‖ ≤ S) {z : ℂ} (hzR : ‖z‖ ≤ R) :
    ‖g z‖ ≤ S * (∏ l ∈ range h, ‖z - (l : ℂ)‖ ^ M) / (R - h) ^ (h * M) := by
  sorry

end Collatz.Gelfond
