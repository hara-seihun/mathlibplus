import Mathlib

namespace MathlibPlus.Open.LinearAlgebra.R0047AffineHankel

noncomputable section

private def responseHankel (N : ℕ) (r : ℝ → ℕ → ℝ) (τ : ℝ) :
    Matrix (Fin N) (Fin N) ℝ :=
  fun i j => r τ (i.1 + j.1 + 1) / 2

/-- Claim 17467: after the response coefficients' affine deformation is
written coefficientwise, the Hankel family has a direction matrix independent
of the real parameter.  The carrier is quantified inside this closed registry
proposition. -/
def affineHankelPencil_claim17467 : Prop :=
  ∀ (N : ℕ), 1 ≤ N →
    ∀ (r : ℝ → ℕ → ℝ) (d : ℕ → ℝ),
      (∀ τ : ℝ, ∀ n : ℕ,
        r τ n = r 1 n + (1 - τ) * d n) →
      ∃ D : Matrix (Fin N) (Fin N) ℝ,
        ∀ τ : ℝ, ∀ i j : Fin N,
          responseHankel N r τ i j =
            responseHankel N r 1 i j + (1 - τ) * D i j

end
end MathlibPlus.Open.LinearAlgebra.R0047AffineHankel
