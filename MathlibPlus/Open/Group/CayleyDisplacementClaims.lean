import Mathlib

noncomputable section

namespace MathlibPlus.Open

/-- The period subgroup/twin criterion for the additive Cayley graph. -/
def translationPeriodTwinCriterion : Prop :=
  ∀ (G : Type*) [AddCommGroup G] (S : Set G),
    let translate : G → Set G := fun g => {x | ∃ s ∈ S, x = s + g}
    let P : Set G := {g | translate g = S}
    let N : G → Set G := fun x => {y | y - x ∈ S}
    (0 ∈ P ∧
      (∀ a b, a ∈ P → b ∈ P → a + b ∈ P) ∧
      (∀ a, a ∈ P → -a ∈ P)) ∧
    ((∀ x y, N x = N y → x = y) ↔
      (∀ g, g ∈ P ↔ g = 0)) ∧
    (∀ g, g ∈ P → g ≠ 0 → ∀ x, N (x + g) = N x)

/-- The displacement-subgroup equality for a permutation of an elementary
abelian 2-group. -/
def displacementSubgroupClaim
    (V : Type*) [AddCommGroup V] (q : Equiv.Perm V)
    (W : AddSubgroup V) : Prop :=
  (∀ v : V, v + v = 0) →
    W = AddSubgroup.closure {w : V | ∃ u : V, w = u + q u + q 0}

/-- The fiber-permutation translation statement modulo its displacement
subspace, including preservation of the quotient coset relation. -/
def fiberPermutationTranslationClaim
    (V : Type*) [AddCommGroup V] (q : Equiv.Perm V)
    (U : AddSubgroup V) : Prop :=
  (∀ v : V, v + v = 0) →
    AddSubgroup.closure {w : V | ∃ u : V, w = u + q u + q 0} ≤ U →
      (∀ v : V,
        {x : V | x - q v ∈ U} = {x : V | x - (v + q 0) ∈ U}) ∧
      (∀ v w : V, v - w ∈ U → q v - q w ∈ U)

end MathlibPlus.Open
