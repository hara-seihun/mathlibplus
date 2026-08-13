import Mathlib.GroupTheory.SpecificGroups.Dihedral

namespace MathlibPlus.Open.GraphTheory

/-- The dihedral group of order fourteen is CI for arbitrary finite families of
directed binary Cayley relations (`CI^(2)`). Loops are allowed; no inverse-
closure, identity-exclusion, connectedness, or generation hypothesis is used. -/
def dihedralFourteenDirectedRelationalCI : Prop :=
  ∀ (κ : Type) [Finite κ]
    (S T : κ → Set (DihedralGroup 7))
    (e : DihedralGroup 7 ≃ DihedralGroup 7),
    (∀ i x y, x⁻¹ * y ∈ S i ↔ (e x)⁻¹ * e y ∈ T i) →
    ∃ α : DihedralGroup 7 ≃* DihedralGroup 7,
      ∀ i, α '' S i = T i

end MathlibPlus.Open.GraphTheory
