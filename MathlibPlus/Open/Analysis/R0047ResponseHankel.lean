import Mathlib

namespace MathlibPlus.Open.Analysis.R0047ResponseHankel

noncomputable section

private def responseHankel (N : ℕ) (r : ℝ → ℕ → ℝ) (τ : ℝ) :
    Matrix (Fin N) (Fin N) ℝ :=
  fun i j => r τ (i.1 + j.1 + 1) / 2

/-- Claim 17463: the response Hankel matrix has the displayed coefficient
entries, with the real deformation parameter and the positive-size indexing
from the source. -/
def responseHankelMatrixDefinition_claim17463 : Prop :=
  ∀ (N : ℕ), 1 ≤ N →
    ∀ (r : ℝ → ℕ → ℝ) (τ : ℝ) (i j : Fin N),
      responseHankel N r τ i j = r τ (i.1 + j.1 + 1) / 2

end
end MathlibPlus.Open.Analysis.R0047ResponseHankel
