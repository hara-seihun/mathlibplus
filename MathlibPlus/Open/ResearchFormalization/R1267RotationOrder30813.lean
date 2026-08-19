import MathlibPlus.Open.ResearchFormalization.BatchR1267

namespace MathlibPlus.Open.ResearchFormalization.R1267RotationOrder30813

open MathlibPlus.Open.ResearchFormalization.BatchR1267

noncomputable section

abbrev Perm (Ω : Type*) := Equiv.Perm Ω

def orbitRestrictionBelongs {Ω : Type*}
    (B : Set Ω) (r : Perm Ω) (O : Subgroup (Perm B)) : Prop :=
  ∃ p : Perm B, p ∈ O ∧
    ∀ b : B, (p b : Ω) = r (b : Ω)

/-- Claim 30813: after the equal quotient action is aligned, the product of
central involutions fixes every literal U-orbit, centralizes literal U, is a
Hall translation on every orbit with order dividing the U-exponent, and has
odd order. -/
def claim30813 {Ω : Type*} [Fintype Ω]
    (U R T : Subgroup (Perm Ω)) (zR zT : Perm Ω) : Prop :=
  (abelianPermutationSubgroup U ∧
    Odd (Nat.card U) ∧
    semiregularPermutationSubgroup U ∧
    regularPermutationSubgroup R ∧
    regularPermutationSubgroup T ∧
    U ≤ R ∧ U ≤ T ∧
    centralInvolution R zR ∧
    centralInvolution T zT ∧
    sameOrbitQuotientAction U zR zT) →
    let r : Perm Ω := zR * zT
    centralizesSubgroup U r ∧
      fixesOrbitPartition U r ∧
      (∀ B : Set Ω, B ∈ orbitPartition U →
        ∃ O : Subgroup (Perm B), ∃ b₀ : B,
          oppositeOrbitAction U B O b₀ ∧
            orbitRestrictionBelongs B r O) ∧
      orderOf r ∣ Monoid.exponent U ∧
      Odd (orderOf r)

end

end MathlibPlus.Open.ResearchFormalization.R1267RotationOrder30813
