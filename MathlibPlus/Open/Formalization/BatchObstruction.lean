import Mathlib

namespace MathlibPlus.Open.FormalizationBatch

noncomputable section

/-- Claim 55795: the exact obstruction to partial C3 inversion. -/
def claim_55795 : Prop := by
  classical
  let G : Type := ZMod 5 × ZMod 3
  let orbit : G → Finset G := fun g => {g, -g}
  let basic : Set (Finset G) := {C | ∃ g : G, g ≠ 0 ∧ C = orbit g}
  let X : Finset G :=
    {((1 : ZMod 5), (1 : ZMod 3)), ((-1 : ZMod 5), (-1 : ZMod 3))}
  let Y : Finset G :=
    {((1 : ZMod 5), (-1 : ZMod 3)), ((-1 : ZMod 5), (1 : ZMod 3))}
  let partialMap : G → G := fun z => (z.1, -z.2)
  exact
    X ∈ basic ∧ Y ∈ basic ∧ X.image partialMap = Y ∧ X ≠ Y

end
end MathlibPlus.Open.FormalizationBatch
