import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.HeavySlabs


def quotientByTwoPointLine
    (W T Z : Type*) [AddCommGroup W]
    (u : W) (π : W → T × Z) : Prop :=
  Function.Surjective π ∧
    u ≠ 0 ∧
      u + u = 0 ∧
        ∀ x y : W, π x = π y ↔ y = x ∨ y = x + u


def heavySelection
    (W T Z : Type*) [AddCommGroup W]
    (u : W) (π : W → T × Z) (t : T) (S : Set W) : Prop :=
  (∀ x : W, (π x).1 = t → x ∈ S ∧ x + u ∈ S) ∧
    (∀ x : W, (π x).1 ≠ t → (x ∈ S ↔ x + u ∉ S))


def autocorrelationEvent
    (W : Type*) [AddCommGroup W]
    (u : W) (S : Set W) : Set W :=
  {x | x ∈ S ∧ x + u ∈ S}


def doubledSlab
    (W T Z : Type*) (π : W → T × Z) (t : T) : Set W :=
  {x | (π x).1 = t}


def claim35715
    (W T Z : Type*) [AddCommGroup W]
    (u : W) (π : W → T × Z) (S : T → Set W) : Prop :=
  quotientByTwoPointLine W T Z u π →
    (∀ t : T, heavySelection W T Z u π t (S t)) →
      (∀ t : T,
        autocorrelationEvent W u (S t) = doubledSlab W T Z π t) ∧
        (∀ t t' : T, t ≠ t' →
          Disjoint (doubledSlab W T Z π t) (doubledSlab W T Z π t'))

end MathlibPlus.Open.ResearchFormalization.HeavySlabs
