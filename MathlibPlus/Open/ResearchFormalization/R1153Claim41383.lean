import MathlibPlus.Open.ResearchFormalization.R1153

namespace MathlibPlus.Open.ResearchFormalization.R1153Claim41383

open MathlibPlus.Open.ResearchFormalization.R1153

/-- Claim 41383: the reviewed exact mixed-even minimum-block carrier gives a
kernel conjugator, a literal common central involution, and its normal
 two-point orbit system for the generated regular copies. -/
def claim41383 : Prop :=
  ∀ {A : Type*} [Fintype A] [CommGroup A],
    Odd (Fintype.card A) →
    ∀ (Ω : Type*) [Fintype Ω]
      (X : Subgroup (Equiv.Perm Ω))
      (R T : Subgroup X)
      (B : Finset (Set Ω))
      (π : X →* Equiv.Perm (BlockType B)),
      Nonempty (R ≃* (A × Q8)) →
      Nonempty (T ≃* (A × Q8)) →
      MathlibPlus.Open.GraphTheory.regularPermutationSubgroup
        (R.map X.subtype) →
      MathlibPlus.Open.GraphTheory.regularPermutationSubgroup
        (T.map X.subtype) →
      Subgroup.closure ((R : Set X) ∪ (T : Set X)) = ⊤ →
      commonNontrivialBlockSystem B →
      (∀ (x : X) (U : BlockType B),
        ((π x) U).1 = ((x : Equiv.Perm Ω) '' U.1)) →
      MathlibPlus.Open.ResearchFormalization.minimumNontrivialBlockSystem
          (X : Set (Equiv.Perm Ω)) (B : Set (Set Ω)) →
      (∀ U : BlockType B,
        mixedEvenBlockType31620 (A := A)
          (↥(kernelIntersection31617 π R)) →
          ∃ δ : π.ker, ∃ z : Equiv.Perm Ω,
            centralInvolution31620 R z ∧
            conjugatedSecondCentralInvolution31620 T (δ.1 : X) z ∧
            normalTwoPointOrbitSystem31620 X z)

end MathlibPlus.Open.ResearchFormalization.R1153Claim41383
