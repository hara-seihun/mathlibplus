import MathlibPlus.Open.ResearchFormalization.R0335

open scoped BigOperators
open MathlibPlus.Open.TreeSpectral

namespace MathlibPlus.Open.ResearchFormalization.R0335

noncomputable section

/-- The automorphism-gauged identification of a transpose attachment row
with the coefficient of the corresponding unlabelled weighted graft. -/
def automorphismGauge (n : ℕ) : Prop :=
  ∀ (C : TreeClass (n - 1)) (k : Fin 4) (T : TreeClass n),
    attachmentMatrixQ n (C, k) T =
      (weightedGraftBasis n k C) T

/-- Claim 20032: after the explicit automorphism-gauge identification, the
transpose attachment map has the four displayed weighted leaf-graft channels
on every card basis vector.  The fresh leaf is represented by
`cardGraftGraph`, and the four exact weights are those in `graftWeight`. -/
def claim20032 : Prop :=
  ∀ n : ℕ, automorphismGauge n →
    ∀ C : TreeClass (n - 1),
      attachmentMapBasis n (C, 0) =
          G₀ n (Finsupp.single C 1) ∧
        attachmentMapBasis n (C, 1) =
          G₁ n (Finsupp.single C 1) ∧
        attachmentMapBasis n (C, 2) =
          G₂Star n (Finsupp.single C 1) ∧
        attachmentMapBasis n (C, 3) =
          G₂Path n (Finsupp.single C 1)

end

end MathlibPlus.Open.ResearchFormalization.R0335
