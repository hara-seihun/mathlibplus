import Mathlib

namespace MathlibPlus.Open.GroupTheory.Claim60265

/-- Inverse closure of a connection set in an additive group. -/
def inverseClosed {G : Type*} [AddGroup G] (S : Set G) : Prop :=
  ∀ x : G, x ∈ S → -x ∈ S

/-- Isomorphism of the ordinary simple undirected Cayley graphs of two
connection sets on the same additive group.  The hypotheses of the claim
ensure that this adjacency relation is loopless and symmetric. -/
def cayleyGraphIsomorphic {G : Type*} [AddGroup G]
    (S T : Set G) : Prop :=
  ∃ f : G → G,
    Function.Bijective f ∧
      ∀ x y : G, (y - x ∈ S ↔ f y - f x ∈ T)

/-- Every valency-13 (or complementary valency-94) connection set on
`C₄ × F₃³` is a CI connection set for ordinary undirected Cayley graphs. -/
def c4_prod_f3_three_valency_thirteen_ci : Prop :=
  let V := Fin 3 → ZMod 3
  let G := ZMod 4 × V
  ∀ (S T : Set G),
    S ⊆ (Set.univ : Set G) \ {0} →
    T ⊆ (Set.univ : Set G) \ {0} →
    inverseClosed S →
    inverseClosed T →
    min (Set.ncard S) (107 - Set.ncard S) = 13 →
    min (Set.ncard T) (107 - Set.ncard T) = 13 →
    cayleyGraphIsomorphic S T →
    ∃ α : G ≃+ G, α '' S = T

end MathlibPlus.Open.GroupTheory.Claim60265
