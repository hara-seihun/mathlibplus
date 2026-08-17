import Mathlib
import MathlibPlus.Open.ResearchFormalizationBatch_01a003d0_6085_7e88_9855_ed1ff0b1b6e8

namespace MathlibPlus.Open.ResearchFormalization.Q0056Claim16279

noncomputable section

/-- The coordinates in the balanced-support construction are exactly the
`s`-subsets of `[m]`. -/
def allSSubsets (m s : ℕ) : Finset (Finset (Fin m)) :=
  (Finset.univ : Finset (Finset (Fin m))).filter (fun S => S.card = s)

/-- The member indexed by `i` consists of precisely the `s`-subset
coordinates containing `i`. -/
def balancedSupportMember (m s : ℕ) (i : Fin m) : Finset (Finset (Fin m)) :=
  (allSSubsets m s).filter (fun S => i ∈ S)

/-- The degree of a coordinate in the indexed balanced family. -/
def balancedCoordinateDegree (m s : ℕ) (S : Finset (Fin m)) : ℕ :=
  ((Finset.univ : Finset (Fin m)).filter
    (fun i => S ∈ balancedSupportMember m s i)).card

/-- An indexed family is three-sunflower-free when no injectively indexed
triple is a sunflower. -/
def indexedThreeSunflowerFree {m : ℕ}
    (A : Fin m → Finset (Finset (Fin m))) : Prop :=
  ∀ I : Fin 3 → Fin m, Function.Injective I →
    ¬ MathlibPlus.Open.ResearchFormalizationBatch_01a003d0_6085_7e88_9855_ed1ff0b1b6e8.isSunflowerTuple
      (fun j => A (I j))

/-- One coordinate for every `s`-subset gives a distinct uniform
three-sunflower-free family, with every coordinate of degree `s`. -/
def balancedSupportsRealizeMediumDegree_16279 : Prop :=
  ∀ (m s : ℕ), 2 ≤ s → s ≤ m - 1 →
    (∀ i : Fin m,
      (balancedSupportMember m s i).card = Nat.choose (m - 1) (s - 1)) ∧
    Function.Injective (balancedSupportMember m s) ∧
    indexedThreeSunflowerFree (fun i => balancedSupportMember m s i) ∧
    (∀ S : Finset (Fin m), S ∈ allSSubsets m s →
      balancedCoordinateDegree m s S = s)

/-- The canonical balanced choice `1 + floor((m-1)/2)` eventually violates
both sides of every fixed rare-or-near-common degree gap. -/
def balancedSupportsDefeatFixedDegreeGaps_16279 : Prop :=
  ∀ D E : ℕ, ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m →
    let s := 1 + (m - 1) / 2
    2 ≤ s ∧ s ≤ m - 1 ∧
      (∀ S : Finset (Fin m), S ∈ allSSubsets m s →
        D < balancedCoordinateDegree m s S ∧
          E < m - balancedCoordinateDegree m s S)

/-- The complete admitted medium-degree construction and its fixed-gap
obstruction. -/
def balancedSupportMediumDegree_16279 : Prop :=
  balancedSupportsRealizeMediumDegree_16279 ∧
    balancedSupportsDefeatFixedDegreeGaps_16279

end
end MathlibPlus.Open.ResearchFormalization.Q0056Claim16279
