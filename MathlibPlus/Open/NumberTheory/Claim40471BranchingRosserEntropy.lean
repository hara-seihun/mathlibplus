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

private def generatedTailCount (y T : ℝ) : ℕ :=
  Set.ncard {path : List ℕ | GeneratedTail y T path}

private def normalizedGeneratedTailCount (y T : ℝ) : ℝ :=
  Real.exp (-T) * (generatedTailCount y T : ℝ)

private def branchingEntropyEstimate (C y : ℝ) : Prop :=
  let L := branchLog y
  let ell := iteratedLog y
  let G := normalizedGeneratedTailCount y L
  0 < G ∧
    0 < ((generatedProducts y).ncard : ℝ) ∧
    |(-Real.log G) - ell ^ 2 / (2 * Real.log 3)| ≤
      C * ell ^ (3 / 2 : ℝ) ∧
    |Real.log ((generatedProducts y).ncard : ℝ) -
        (L - ell ^ 2 / (2 * Real.log 3))| ≤
      C * ell ^ (3 / 2 : ℝ)

/-- The entropy asymptotic for the exact branching logarithmic-bin family.
The normalized quantity is the exponential normalization of the count of
recursive generated tails, while the cardinality estimate is for the product
image of the same root-generated paths, not for the full Rosser support. -/
def branchingRosserFamilyEntropy_claim40471 : Prop :=
  ∃ C Y₀ : ℝ, 0 < C ∧ 2 ≤ Y₀ ∧
    ∀ y : ℝ, Y₀ ≤ y → branchingEntropyEstimate C y

end
end MathlibPlus.Open.NumberTheory
