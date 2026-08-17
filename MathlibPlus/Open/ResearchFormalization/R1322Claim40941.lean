import MathlibPlus.Open.ResearchFormalization.BatchGroupClaims
import MathlibPlus.Open.ResearchFormalization.MinimumBlockAction
import MathlibPlus.Open.BatchFormalization.GroupClaims

namespace MathlibPlus.Open.ResearchFormalization.R1322

open MathlibPlus.Open.ResearchFormalization
open MathlibPlus.Open.BatchFormalization

/-- Conjugation of a permutation subgroup by an ambient permutation. -/
def conjugateSubgroup {Ω : Type*}
    (g : Equiv.Perm Ω) (H : Subgroup (Equiv.Perm Ω)) :
    Subgroup (Equiv.Perm Ω) :=
  Subgroup.map ((MulAut.conj g).toMonoidHom) H

/-- The literal family `𝒜 = {Aᵢ^g : i ∈ {1,2}, g ∈ G}`. -/
def conjugateSubgroupFamily {Ω : Type*}
    (G : Subgroup (Equiv.Perm Ω))
    (A : Fin 2 → Subgroup (Equiv.Perm Ω)) :
    Set (Subgroup (Equiv.Perm Ω)) :=
  {H | ∃ i : Fin 2, ∃ g : G,
    H = conjugateSubgroup (g : Equiv.Perm Ω) (A i)}

/-- The subgroup induced on a block by all well-defined restrictions of `H`. -/
def localRestrictionSubgroup {Ω : Type*}
    (H : Subgroup (Equiv.Perm Ω)) (B : Set Ω) :
    Subgroup (Equiv.Perm B) :=
  Subgroup.closure
    {q | ∃ h : H, ∃ hh : (h : Equiv.Perm Ω) '' B = B,
      q = restrictPermutation (h : Equiv.Perm Ω) B hh}

/-- Commutativity of the normal closure, on its actual permutation carrier. -/
def isAbelianPermutationSubgroup {Ω : Type*}
    (H : Subgroup (Equiv.Perm Ω)) : Prop :=
  ∀ x y : H,
    (x : Equiv.Perm Ω) * (y : Equiv.Perm Ω) =
      (y : Equiv.Perm Ω) * (x : Equiv.Perm Ω)

/-- The singleton local-restriction alternative in Record 2. -/
def hasOneRegularCyclicRestrictionOnEveryBlock {Ω : Type*}
    (m : ℕ) (blocks : Set (Set Ω))
    (family : Set (Subgroup (Equiv.Perm Ω))) : Prop :=
  ∀ B : Set Ω, B ∈ blocks →
    ∃! L : Subgroup (Equiv.Perm B),
      IsRegularCyclicAction m L ∧
        ∀ H : Subgroup (Equiv.Perm Ω), H ∈ family →
          localRestrictionSubgroup H B = L

/-- A coordinate product of cyclic translations, with one coordinate per block. -/
def isNormalSubdirectCoordinateTranslationModule
    {Ω : Type*} [Fintype Ω]
    (m : ℕ) (blocks : Set (Set Ω))
    (N : Subgroup (Equiv.Perm Ω)) : Prop :=
  ∃ e : (∀ B : blocks, B ≃ Multiplicative (ZMod m)),
    ∃ P : Subgroup (blocks → Multiplicative (ZMod m)),
      ∃ Φ : N ≃* P,
        P.Normal ∧
          (∀ B : blocks, ∀ z : Multiplicative (ZMod m),
            ∃ u : P, (u : blocks → Multiplicative (ZMod m)) B = z) ∧
          (∀ n : N, ∀ B : blocks,
            (n : Equiv.Perm Ω) '' (B : Set Ω) = (B : Set Ω)) ∧
          (∀ n : N, ∀ B : blocks,
            ∀ hB : (n : Equiv.Perm Ω) '' (B : Set Ω) = (B : Set Ω),
            ∀ x : (B : Set Ω),
              e B (restrictPermutation (n : Equiv.Perm Ω)
                (B : Set Ω) hB x) =
                e B x * (Φ n : blocks → Multiplicative (ZMod m)) B)

/-- Claim 40941: the abelian normal-closure, singleton local restriction, and
normal-subdirect coordinate-translation alternatives are equivalent under the
exact Record 2 carrier. -/
def claim40941 : Prop :=
  ∀ (Ω : Type*) [Fintype Ω]
    (G : Subgroup (Equiv.Perm Ω)) (blocks : Set (Set Ω))
    (m : ℕ) (A : Fin 2 → Subgroup (Equiv.Perm Ω)),
    IsBlockSystem blocks →
    PreservesBlockSystem G blocks →
    (∀ i : Fin 2,
      A i ≤ G ∧
      CyclicPermutationSubgroupOfOrder (A i) m ∧
      HasBlockOrbits (A i) blocks) →
    let family := conjugateSubgroupFamily G A
    let N := normalClosureOfConjugates G A
    (∀ h : N, (h : Equiv.Perm Ω) ∈ blockKernel G blocks) ∧
      (isAbelianPermutationSubgroup N ↔
        hasOneRegularCyclicRestrictionOnEveryBlock m blocks family) ∧
      (isAbelianPermutationSubgroup N ↔
        isNormalSubdirectCoordinateTranslationModule m blocks N)

end MathlibPlus.Open.ResearchFormalization.R1322
