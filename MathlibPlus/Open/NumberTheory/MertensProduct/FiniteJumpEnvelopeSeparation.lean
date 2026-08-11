import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.PrimeCounting

/-!
# Finite Mertens-product jump-envelope separation

Statement-fidelity registry node for admitted claim 662.
-/

open scoped BigOperators

noncomputable section

namespace MathlibPlus.Open.NumberTheory.MertensProduct

/-- Between the left endpoint `286` and the analytic handoff `2278382`, every
later prime jump of the normalized Mertens-product error lies strictly below the
error at `286`. The unique closest later jump is at `293`, with the displayed
strict gap. The two finite enumeration counts are included in the obligation. -/
def finiteJumpEnvelopeSeparation : Prop :=
  let P : ℕ → ℝ := fun n =>
    ∏ p ∈ Nat.primesLE n, (p : ℝ) / ((p : ℝ) - 1)
  let E : ℕ → ℝ := fun n =>
    Real.log n *
      (Real.exp (-Real.eulerMascheroniConstant) * P n - Real.log n)
  (∀ p : ℕ, p.Prime → 286 < p → p ≤ 2278382 →
      E p < E 286 ∧ E p ≤ E 293 ∧ (p ≠ 293 → E p < E 293)) ∧
    E 286 - E 293 > (118014 : ℝ) / 5000000 ∧
    Nat.primeCounting 2278382 = 168064 ∧
    ((Nat.primesLE 2278382).filter fun p => 286 < p).card = 168003

end MathlibPlus.Open.NumberTheory.MertensProduct
