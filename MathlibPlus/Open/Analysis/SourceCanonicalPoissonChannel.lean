import Mathlib

namespace MathlibPlus.Open.Analysis

noncomputable section

/-- The logarithmic Poisson kernel `K_q` from the admitted source context. -/
def poissonKernel (q : ℝ → ℝ) (x : ℝ) : ℝ :=
  Real.exp (x / 2) * ∑' n : {n : ℕ // 1 ≤ n}, q ((n.1 : ℝ) * Real.exp x)

/--
The exact source-canonical channel specification.  The parameters `κ`, `H`,
`F`, and `D` are the named objects being defined by the claim; the
conjunction records each of their defining equations without introducing a
new carrier or a proof of the open statement.
-/
def sourceCanonicalFullLiteralDefectClaim
    (q : ℝ → ℝ) (L : ℝ)
    (κ : ℝ → ℝ) (H F D : ℂ → ℂ) : Prop :=
  (∀ x : ℝ, κ x =
    (poissonKernel q x + poissonKernel q (-x)) / 2) ∧
  (∀ z : ℂ, H z =
    ∫ t : ℝ, (κ t : ℂ) * Complex.exp (Complex.I * z * (t : ℂ))) ∧
  (∀ z : ℂ, F z =
    ∫ t in (-L)..L, (κ t : ℂ) * Complex.exp (Complex.I * z * (t : ℂ))) ∧
  (∀ z : ℂ, D z = F z - H z)

end

end MathlibPlus.Open.Analysis
