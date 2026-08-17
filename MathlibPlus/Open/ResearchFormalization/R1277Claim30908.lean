import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R1277Claim30908

abbrev A := Fin 3 → ZMod 2
abbrev B := ZMod 3 × ZMod 3
abbrev G := A × B

/-- The displacement subgroup of a fiber permutation in the additive fiber
`B = C₃²`. -/
def displacementSubgroup (q : Equiv.Perm B) : AddSubgroup B :=
  AddSubgroup.closure (Set.range (fun t : B => t - q t + q 0))

/-- The route hypothesis at the three marked base positions `2,3,4`.  The
subgroups are joined as additive subgroups, and “proper” is retained as a
strict subgroup inequality rather than merely non-equality of carriers. -/
def claim30908 (q : Fin 8 → Equiv.Perm B) : Prop :=
  let w₂ := displacementSubgroup (q 2)
  let w₃ := displacementSubgroup (q 3)
  let w₄ := displacementSubgroup (q 4)
  w₂ ⊔ w₃ ⊔ w₄ = ⊤ ∧
    ((w₂ = ⊤ ∧ w₃ < ⊤ ∧ w₄ < ⊤) ∨
      (w₃ = ⊤ ∧ w₂ < ⊤ ∧ w₄ < ⊤) ∨
      (w₄ = ⊤ ∧ w₂ < ⊤ ∧ w₃ < ⊤))

end MathlibPlus.Open.ResearchFormalization.R1277Claim30908
