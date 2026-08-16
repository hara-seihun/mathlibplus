import Mathlib

namespace MathlibPlus.Open.CI

inductive EC35C8Generator
  | a
  | t

open EC35C8Generator

def EC35C8Relators : Set (FreeGroup EC35C8Generator) :=
  { (FreeGroup.of a) ^ 35,
    (FreeGroup.of t) ^ 8,
    (FreeGroup.of t) * (FreeGroup.of a) * (FreeGroup.of t)⁻¹ * (FreeGroup.of a) }

abbrev EC35C8 := PresentedGroup EC35C8Relators

def EC35C8A : EC35C8 := PresentedGroup.mk EC35C8Relators (FreeGroup.of a)

def EC35C8T : EC35C8 := PresentedGroup.mk EC35C8Relators (FreeGroup.of t)

def EC35C8CayleyAdjacency (S : Set EC35C8) (x y : EC35C8) : Prop :=
  x⁻¹ * y ∈ S

def EC35C8CayleyGraphIsomorphic (S T : Set EC35C8) : Prop :=
  ∃ e : EC35C8 ≃ EC35C8,
    ∀ x y : EC35C8,
      EC35C8CayleyAdjacency S x y ↔
        EC35C8CayleyAdjacency T (e x) (e y)

def ciEC35C8SquarefreeResidualM35Valencies9270 : Prop :=
  ∀ S T : Set EC35C8,
    (S ⊆ (Set.univ : Set EC35C8) \ {1} ∧
      ∀ ⦃x : EC35C8⦄, x ∈ S → x⁻¹ ∈ S) →
    (T ⊆ (Set.univ : Set EC35C8) \ {1} ∧
      ∀ ⦃x : EC35C8⦄, x ∈ T → x⁻¹ ∈ T) →
    (S.ncard = T.ncard ∧ (S.ncard = 9 ∨ S.ncard = 270)) →
    EC35C8CayleyGraphIsomorphic S T →
    ∃ α : EC35C8 ≃* EC35C8, Set.image α S = T

end MathlibPlus.Open.CI
