import Mathlib

namespace MathlibPlus.Open.NumberTheory

noncomputable section

private def branchLog (y : ℝ) : ℝ := Real.log y
private def iteratedLog (y : ℝ) : ℝ := Real.log (branchLog y)
private def branchDelta (y : ℝ) : ℝ := (Real.sqrt (iteratedLog y))⁻¹
private def branchHeight (y : ℝ) : ℝ := iteratedLog y

private def primeInLogBin (w : ℤ) (p : ℕ) : Prop :=
  Nat.Prime p ∧
    Real.exp ((w : ℝ) - 1) < (p : ℝ) ∧
    (p : ℝ) ≤ Real.exp (w : ℝ)

/-- The exact recursive logarithmic-bin paths: an active state chooses the
integer odd-bin index, its displayed floor-defined even-bin index, one prime
from each bin, and then recurses with the remaining logarithmic budget. -/
private inductive GeneratedTail (y : ℝ) : ℝ → List ℕ → Prop
  | stop {T : ℝ} (hT : T ≤ branchHeight y) : GeneratedTail y T []
  | step {T : ℝ} {u v : ℤ} {p q : ℕ} {tail : List ℕ}
      (hactive : branchHeight y < T)
      (hu : ((1 - branchDelta y) / 2) * T ≤ (u : ℝ) ∧
        (u : ℝ) ≤ ((1 - branchDelta y / 2) / 2) * T)
      (hv : v = ⌊(T - (u : ℝ) - 6) / 3⌋)
      (hp : primeInLogBin u p)
      (hq : primeInLogBin v q)
      (hrec : GeneratedTail y (T - (u : ℝ) - (v : ℝ)) tail) :
      GeneratedTail y T (p :: q :: tail)

private def generatedProducts (y : ℝ) : Set ℕ :=
  {m | ∃ path : List ℕ,
    GeneratedTail y (branchLog y) path ∧ path.prod = m}

/-- The generated logarithmic-bin family itself remains little-o of the
Rosser target scale.  The family is tied to the source construction rather
than represented by an unrelated callback; the final clause is the exact
asymptotic limitation of this branching mechanism. -/
def branchingRosserFamilySubcritical_claim40474 : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ Y : ℝ, 2 ≤ Y ∧
    ∀ y : ℝ, Y ≤ y →
      (generatedProducts y).ncard ≤
        ε * (y / (Real.log y) ^ 2)

end
end MathlibPlus.Open.NumberTheory
