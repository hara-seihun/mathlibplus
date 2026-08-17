import Mathlib
import MathlibPlus.Open.ResearchFormalizationBatch_01a003d0_6085_7e88_9855_ed1ff0b1b6e8

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.Q0056Claim16265

open MathlibPlus.Open.ResearchFormalizationBatch_01a003d0_6085_7e88_9855_ed1ff0b1b6e8

noncomputable section

/-- Integer multiplicities on the nonempty supports of `[m]`, with the two
exact-two/exact-one support-cover constraints. -/
def integerSupportCover (m : ℕ) (z : Finset (Fin m) → ℕ) : Prop :=
  (∀ S : Finset (Fin m), S.Nonempty ∨ z S = 0) ∧
    (∀ I : Finset (Fin m), I.card = 3 →
      1 ≤ ∑ S : Finset (Fin m),
        if (S ∩ I).card = 2 then z S else 0) ∧
    (∀ i j : Fin m, i ≠ j →
      1 ≤ ∑ S : Finset (Fin m),
        if (S ∩ {i, j}).card = 1 then z S else 0)

/-- The member load induced by an integer support cover. -/
def integerSupportLoad (m : ℕ) (z : Finset (Fin m) → ℕ) (i : Fin m) : ℕ :=
  ∑ S : Finset (Fin m), if i ∈ S then z S else 0

/-- An indexed family is three-sunflower-free when no injectively indexed
triple is a sunflower. -/
def indexedThreeSunflowerFree {α : Type*} [DecidableEq α] {m : ℕ}
    (A : Fin m → Finset α) : Prop :=
  ∀ I : Fin 3 → Fin m, Function.Injective I →
    ¬ isSunflowerTuple (fun j => A (I j))

/-- The finite-ground realization carrier for a distinct uniform family. -/
def indexedUniformDistinctThreeSunflowerFree (m n g : ℕ)
    (A : Fin m → Finset (Fin g)) : Prop :=
  (∀ i : Fin m, (A i).card = n) ∧
    Function.Injective A ∧
    indexedThreeSunflowerFree A

/-- There is a distinct uniform three-sunflower-free `m`-member family at
uniformity `n`. -/
def hasThreeSunflowerFreeFamilyAtUniformity (m n : ℕ) : Prop :=
  ∃ g : ℕ, ∃ A : Fin m → Finset (Fin g),
    indexedUniformDistinctThreeSunflowerFree m n g A

/-- A number is a least possible integer-cover maximum load. -/
def isLeastIntegerSupportMaximum (m d : ℕ) : Prop :=
  (∃ z : Finset (Fin m) → ℕ,
    integerSupportCover m z ∧
      (∀ i : Fin m, integerSupportLoad m z i ≤ d) ∧
      (∀ e : ℕ, (∀ i : Fin m, integerSupportLoad m z i ≤ e) → d ≤ e)) ∧
    (∀ z : Finset (Fin m) → ℕ, integerSupportCover m z →
      ∀ e : ℕ, (∀ i : Fin m, integerSupportLoad m z i ≤ e) → d ≤ e)

/-- A number is the least uniformity supporting a distinct `m`-member
three-sunflower-free family. -/
def isLeastSupportingUniformity (m d : ℕ) : Prop :=
  (hasThreeSunflowerFreeFamilyAtUniformity m d) ∧
    (∀ n : ℕ, hasThreeSunflowerFreeFamilyAtUniformity m n → d ≤ n)

/-- Exact integer support-cover formulation for three sunflowers: the minimum
maximum support load equals the least supporting uniformity, every bound is
preserved in both directions, and every feasible cover is realized at its own
maximum load by multiplicity points and private singleton padding. -/
def exactIntegerSupportCoverFormulation_16265 : Prop :=
  (∀ (m r : ℕ),
    (∃ z : Finset (Fin m) → ℕ,
      integerSupportCover m z ∧
        ∀ i : Fin m, integerSupportLoad m z i ≤ r) ↔
    ∃ g : ℕ, ∃ A : Fin m → Finset (Fin g),
      indexedUniformDistinctThreeSunflowerFree m r g A) ∧
  (∀ m : ℕ,
    ∃ d : ℕ,
      isLeastIntegerSupportMaximum m d ∧
        isLeastSupportingUniformity m d ∧
        (∀ z : Finset (Fin m) → ℕ, integerSupportCover m z →
          ∃ d' : ℕ,
            (∀ i : Fin m, integerSupportLoad m z i ≤ d') ∧
              (∀ e : ℕ,
                (∀ i : Fin m, integerSupportLoad m z i ≤ e) → d' ≤ e) ∧
              ∃ g : ℕ, ∃ A : Fin m → Finset (Fin g),
                (∀ i : Fin m, (A i).card = d') ∧
                  Function.Injective A ∧
                  indexedThreeSunflowerFree A ∧
                  (∀ S : Finset (Fin m), S.Nonempty →
                    z S ≤ supportMultiplicity A S) ∧
                  (∀ S : Finset (Fin m), 2 ≤ S.card →
                    supportMultiplicity A S = z S)))

end
end MathlibPlus.Open.ResearchFormalization.Q0056Claim16265
