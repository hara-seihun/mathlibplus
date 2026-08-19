import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R4941ReflectionTransfer

noncomputable section

/-- Claim 53089: polynomial reflection is an involution at every finite
logarithmic-moment order, and every entrywise nonnegative majorant of an
involutive normalized homogeneous core has spectral radius at least one. -/
def reflectionTransfer_claim53089 : Prop :=
  ∀ (d : ℕ) (L : ℝ),
    let R : Polynomial ℝ → Polynomial ℝ := fun p =>
      p.comp (Polynomial.C L - Polynomial.X)
    (∀ p : Polynomial ℝ, p.natDegree ≤ d → R (R p) = p) ∧
      ∀ (A M : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ),
        A ^ 2 = 1 →
          (∀ i j : Fin (d + 1),
            0 ≤ M i j ∧ |A i j| ≤ M i j) →
            1 ≤ spectralRadius ℝ M

end

end MathlibPlus.Open.ResearchFormalization.R4941ReflectionTransfer
