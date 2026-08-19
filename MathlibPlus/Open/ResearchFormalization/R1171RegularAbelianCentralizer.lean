import MathlibPlus.Open.ResearchFormalization.R1171Claim31830

namespace MathlibPlus.Open.ResearchFormalization.R1171RegularAbelianCentralizer

noncomputable section

/-- Claim 31819: for a regular copy of a commutative group in a symmetric
group, the opposite regular representation is the displayed copy, so the
centralizer is exactly that copy. -/
def regularAbelianPermutationCentralizer_claim31819 : Prop :=
  ∀ {G Ω : Type*} [CommGroup G]
    (R : Subgroup (Equiv.Perm Ω)) (e : G ≃ Ω),
    (R : Set (Equiv.Perm Ω)) =
      Set.range (fun g : G =>
        (e.symm.trans (Equiv.mulLeft g)).trans e) →
      Subgroup.centralizer (R : Set (Equiv.Perm Ω)) =
        (R : Set (Equiv.Perm Ω))

end

end MathlibPlus.Open.ResearchFormalization.R1171RegularAbelianCentralizer
