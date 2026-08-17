import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R1171Claim31830

noncomputable section

/-- The transported opposite regular representation in the exact displayed
regular-permutation carrier. -/
def transportedRightRegularCopy
    {G Ω : Type*} [Group G]
    (e : G ≃ Ω) : Set (Equiv.Perm Ω) :=
  Set.range (fun a : G => (e.symm.trans (Equiv.mulRight a)).trans e)

/-- Claim 31830: the centralizer of a displayed regular copy is the opposite
regular representation; without abelianness it need not be the displayed
copy itself. -/
def regularAbeliannessIsLoadBearing_claim31830 : Prop :=
  ∀ {G Ω : Type*} [Group G]
    (R : Subgroup (Equiv.Perm Ω)) (e : G ≃ Ω),
    (R : Set (Equiv.Perm Ω)) =
      Set.range (fun g : G =>
        (e.symm.trans (Equiv.mulLeft g)).trans e) →
      Subgroup.centralizer (R : Set (Equiv.Perm Ω)) =
          transportedRightRegularCopy e ∧
        ((¬ ∀ x y : G, x * y = y * x) →
          Subgroup.centralizer (R : Set (Equiv.Perm Ω)) ≠
            (R : Set (Equiv.Perm Ω)))

end

end MathlibPlus.Open.ResearchFormalization.R1171Claim31830
