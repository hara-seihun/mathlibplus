import MathlibPlus.Open.ResearchFormalization.Batch.Analysis

noncomputable section

namespace MathlibPlus.Open.ResearchFormalization.C0226

open MathlibPlus.Open.ResearchFormalization.Batch

/-- Claim 3301: the diagonal of the inverse normalized Cauchy Gram matrix is
exactly the reciprocal square of the corresponding half-plane separation
product. -/
def claim3301_exactNormalizedCauchyInverseDiagonal
    (n : ℕ) (y t : Fin n → ℝ) : Prop :=
  (∀ j : Fin n, 0 < y j) →
    Function.Injective (fun j : Fin n =>
      halfPlaneParameter (y j) (t j)) →
      let s : Fin n → ℂ := fun j => halfPlaneParameter (y j) (t j)
      let K : Matrix (Fin n) (Fin n) ℂ := fun j k =>
        ((2 : ℂ) * Real.sqrt (y j * y k)) /
          (s j + star (s k))
      ∀ j : Fin n,
        (K⁻¹) j j = ((separationProduct s j : ℂ)⁻¹) ^ (2 : ℕ)

end MathlibPlus.Open.ResearchFormalization.C0226
