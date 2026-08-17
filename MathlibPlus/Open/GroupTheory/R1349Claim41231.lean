import MathlibPlus.Open.GroupTheory.R1349Claim41243
import MathlibPlus.Open.GroupTheory.R1349Claim41244
import MathlibPlus.Open.ResearchFormalization.MinimumBlockAction

namespace MathlibPlus.Open.GroupTheory.R1349Claim41231

open MathlibPlus.Open.GroupTheory.R1349Claim41243
open MathlibPlus.Open.GroupTheory.R1349Claim41244
open MathlibPlus.Open.ResearchFormalization

def blockProjection (K : Subgroup Base) (i : Fin 7) :
    Set (Equiv.Perm (Fin 12)) :=
  {σ | ∃ k : K, k.1 i = σ}

def regularQ12Restriction (H : Set (Equiv.Perm (Fin 12))) : Prop :=
  ∃ Q : Subgroup (Equiv.Perm (Fin 12)),
    Nonempty (Q ≃* Q12) ∧
      (∀ q : Q, (q : Equiv.Perm (Fin 12)) ∈ H) ∧
        ∀ x y : Fin 12, ∃! q : Q,
          (q : Equiv.Perm (Fin 12)) x = y

def sevenCycleIn (H : Set (Equiv.Perm (Fin 12))) : Prop :=
  ∃ σ : Equiv.Perm (Fin 12),
    σ ∈ H ∧
      orderOf σ = 7 ∧
        σ.cycleType = {7, 1, 1, 1, 1, 1}

def oddRegularOrderFourIn (H : Set (Equiv.Perm (Fin 12))) : Prop :=
  ∃ σ : Equiv.Perm (Fin 12),
    σ ∈ H ∧
      orderOf σ = 4 ∧
        σ.cycleType = {4, 4, 4} ∧
          Equiv.Perm.sign σ = (-1 : ℤˣ)

def claim41231 : Prop :=
  ∀ K : Subgroup Base,
    7 ∣ Nat.card K →
    (∀ i : Fin 7, regularQ12Restriction (blockProjection K i)) →
    (∀ i : Fin 7, sevenCycleIn (blockProjection K i)) →
    (∀ i : Fin 7,
      primitivePermutationSet (blockProjection K i)) →
    ∀ i : Fin 7,
      permutationSetTransitive (blockProjection K i) ∧
        (∀ a : A12,
          (a : Equiv.Perm (Fin 12)) ∈ blockProjection K i) ∧
          blockProjection K i = Set.univ ∧
            oddRegularOrderFourIn (blockProjection K i)

end MathlibPlus.Open.GroupTheory.R1349Claim41231
