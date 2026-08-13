import Mathlib

namespace MathlibPlus.Open.GroupTheory

/-- Faithful registry node for the degree-three perfect-transitive
obstruction.  Transitivity is stated as the orbit of the base point 0 in
Fin 3; the active-prime consequence is source-specific and not invented here. -/
def degreeThreePerfectTransitiveSubgroup_claim39421 : Prop :=
  ∀ H : Subgroup (Equiv.Perm (Fin 3)),
    (∀ x : Fin 3,
      ∃ h : H, (h : Equiv.Perm (Fin 3)) 0 = x) →
    Group.IsPerfect H →
    H = ⊥

end MathlibPlus.Open.GroupTheory
