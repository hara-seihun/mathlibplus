import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R0022Claim9627

private def partialCompose {A B C : Type*}
    (outer : B → Option C) (inner : A → Option B) : A → Option C :=
  fun input => (inner input).bind outer

/-- Claim 9627: ordinary typed compositions, finite matrix products, and
ordinary option-valued partial compositions agree under both bracketings.
Typed carriers cover the ordinary chart, interval, and proof-map cases; the
option-valued form records the phrase "where both bracketings are defined". -/
def ordinaryTargetCompositionAssociative_claim9627 : Prop :=
  (∀ {A B C D : Type*}
      (outer : C → D) (middle : B → C) (inner : A → B),
      (outer ∘ middle) ∘ inner = outer ∘ (middle ∘ inner)) ∧
    (∀ {R : Type*} {n : ℕ} [Semiring R]
      (first second third : Matrix (Fin n) (Fin n) R),
      (first * second) * third = first * (second * third)) ∧
    (∀ {A B C D : Type*}
      (outer : C → Option D) (middle : B → Option C)
      (inner : A → Option B),
      partialCompose outer (partialCompose middle inner) =
        partialCompose (partialCompose outer middle) inner)

end MathlibPlus.Open.ResearchFormalization.R0022Claim9627
