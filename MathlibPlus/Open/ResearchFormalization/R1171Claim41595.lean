import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R1171Claim41595

noncomputable section

/-- Claim 41595: in a displayed regular permutation copy the centralizer is
transported right regularity, and the displayed copy cannot be recovered from
that centralizer without the abelian hypothesis. -/
def claim41595 : Prop :=
  ∀ {G Ω : Type*} [Group G]
    (R : Subgroup (Equiv.Perm Ω)) (e : G ≃ Ω),
    (R : Set (Equiv.Perm Ω)) =
      Set.range (fun g : G =>
        (e.symm.trans (Equiv.mulLeft g)).trans e) →
      Subgroup.centralizer (R : Set (Equiv.Perm Ω)) =
          Set.range (fun a : G =>
            (e.symm.trans (Equiv.mulRight a)).trans e) ∧
        ((¬ ∀ x y : G, x * y = y * x) →
          Subgroup.centralizer (R : Set (Equiv.Perm Ω)) ≠
            (R : Set (Equiv.Perm Ω)))

end

end MathlibPlus.Open.ResearchFormalization.R1171Claim41595
