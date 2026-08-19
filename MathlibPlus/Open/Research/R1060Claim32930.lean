import MathlibPlus.Open.Research.FormalizationBatchSemidirect

namespace MathlibPlus.Open.Research.R1060Claim32930

open MathlibPlus.Open.Research.BatchSemidirect

noncomputable section

abbrev PrimeSemidirectCarrier (p : ℕ) (H : Type*) := ZMod p × H

private def relationalAutomorphisms {J Ω : Type*}
    (relations : J → Ω → Ω → Prop) : Set (Equiv.Perm Ω) :=
  {u | ∀ j x y,
    relations j x y ↔ relations j (u x) (u y)}

private def regularRelationalCopy
    {p : ℕ} {H J Ω : Type*} [Group H]
    (χ : H →* (ZMod p)ˣ)
    (relations : J → Ω → Ω → Prop)
    (R : Subgroup (Equiv.Perm Ω))
    (ρ : PrimeSemidirectCarrier p H → Equiv.Perm Ω) : Prop :=
  Nonempty Ω ∧
    Set.range ρ = (R : Set (Equiv.Perm Ω)) ∧
    (∀ r : Equiv.Perm Ω, r ∈ R → r ∈ relationalAutomorphisms relations) ∧
    Function.Injective ρ ∧
    ρ (0, (1 : H)) = 1 ∧
    (∀ g h : PrimeSemidirectCarrier p H,
      ρ (semidirectMultiply χ g h) = ρ g * ρ h) ∧
    (∀ x y : Ω, ∃! g : PrimeSemidirectCarrier p H, ρ g x = y)

private def normalPrimeKernel
    {p : ℕ} {H Ω : Type*} [Group H]
    (χ : H →* (ZMod p)ˣ)
    (ρ : PrimeSemidirectCarrier p H → Equiv.Perm Ω) : Prop :=
  ∀ g : PrimeSemidirectCarrier p H, ∀ a : ZMod p,
    ∃ b : ZMod p,
      ρ (semidirectMultiply χ
          (semidirectMultiply χ g (a, (1 : H)))
          (semidirectInverse χ g)) =
        ρ (b, (1 : H))

private def primeKernelOrbit
    {p : ℕ} {H Ω : Type*} [Group H]
    (ρ : PrimeSemidirectCarrier p H → Equiv.Perm Ω)
    (x : Ω) : Set Ω :=
  {y | ∃ a : ZMod p, ρ (a, (1 : H)) x = y}

private def primeKernelBlocks
    {p : ℕ} {H Ω : Type*} [Group H]
    (ρ : PrimeSemidirectCarrier p H → Equiv.Perm Ω) : Set (Set Ω) :=
  {B | ∃ x : Ω, primeKernelOrbit ρ x = B}

private def samePrimeKernelOrbitPartition
    {p : ℕ} {H Ω : Type*} [Group H] [Fintype Ω]
    (ρR ρT : PrimeSemidirectCarrier p H → Equiv.Perm Ω) : Prop :=
  primeKernelBlocks ρR = primeKernelBlocks ρT ∧
    (∀ x : Ω,
      Nat.card {y : Ω // y ∈ primeKernelOrbit ρR x} = p) ∧
    (∀ x : Ω,
      Nat.card {y : Ω // y ∈ primeKernelOrbit ρT x} = p)

private def inducedQuotientPermutationGroup
    {Ω : Type*}
    (B : Set (Set Ω))
    (R : Subgroup (Equiv.Perm Ω)) :
    Set (Equiv.Perm {C : Set Ω // C ∈ B}) :=
  {q | ∃ r : Equiv.Perm Ω, r ∈ R ∧
    ∀ C : {C : Set Ω // C ∈ B},
      (q C : Set Ω) = r '' (C : Set Ω)}

private def equalInducedQuotientPermutationGroups
    {p : ℕ} {H Ω : Type*} [Group H] [Fintype Ω]
    (ρR ρT : PrimeSemidirectCarrier p H → Equiv.Perm Ω)
    (R T : Subgroup (Equiv.Perm Ω)) : Prop :=
  ∃ B : Set (Set Ω),
    B = primeKernelBlocks ρR ∧
      B = primeKernelBlocks ρT ∧
        inducedQuotientPermutationGroup B R =
          inducedQuotientPermutationGroup B T

private def conjugationCharacter
    {p : ℕ} {H Ω : Type*} [Group H]
    (χ : H →* (ZMod p)ˣ)
    (ρ : PrimeSemidirectCarrier p H → Equiv.Perm Ω) : Prop :=
  ∀ h : H, ∀ a : ZMod p,
    ρ (0, h) * ρ (a, (1 : H)) * (ρ (0, h))⁻¹ =
      ρ ((χ h : ZMod p) * a, (1 : H))

/-- Equal prime-kernel blocks, literal quotient permutation groups, and the
same character action force conjugacy of regular semidirect copies inside the
finite relational automorphism group. -/
def claim32930_equalQuotientAndCharacterConjugacy : Prop :=
  ∀ (p : ℕ), (hp : Nat.Prime p) →
    letI : Fact p.Prime := ⟨hp⟩
    ∀ (H : Type*) [Fintype H] [Group H],
      ¬p ∣ Fintype.card H →
        ∀ (χ : H →* (ZMod p)ˣ),
          ∀ (J : Type*) [Fintype J]
            (Ω : Type*) [Fintype Ω]
            (relations : J → Ω → Ω → Prop)
            (R T : Subgroup (Equiv.Perm Ω))
            (ρR ρT : PrimeSemidirectCarrier p H → Equiv.Perm Ω),
            regularRelationalCopy χ relations R ρR →
              regularRelationalCopy χ relations T ρT →
                normalPrimeKernel χ ρR →
                  normalPrimeKernel χ ρT →
                    samePrimeKernelOrbitPartition ρR ρT →
                      equalInducedQuotientPermutationGroups ρR ρT R T →
                        conjugationCharacter χ ρR →
                          conjugationCharacter χ ρT →
                            ∃ u : Equiv.Perm Ω,
                              u ∈ relationalAutomorphisms relations ∧
                                Set.image
                                    (fun r : Equiv.Perm Ω => u * r * u⁻¹)
                                    (R : Set (Equiv.Perm Ω)) =
                                  (T : Set (Equiv.Perm Ω))

end

end MathlibPlus.Open.Research.R1060Claim32930
