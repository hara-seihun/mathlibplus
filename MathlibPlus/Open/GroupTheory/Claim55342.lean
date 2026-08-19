import Mathlib

namespace MathlibPlus.Open.GroupTheory.Claim55342

/-- Claim 55342: intersections of left cosets are empty or a left coset of
 the subgroup intersection, with the corresponding finite cardinality. -/
def claim55342 : Prop :=
  ∀ {G : Type*} [Finite G] [Group G]
    (U V : Subgroup G) (x y : G),
    let xU : Set G := {w | ∃ u : U, w = x * (u : G)}
    let yV : Set G := {w | ∃ v : V, w = y * (v : G)}
    let I : Set G := xU ∩ yV
    (I = ∅ ∨
      ∀ z : G, z ∈ I →
        I = {w | ∃ h : (U ⊓ V : Subgroup G), w = z * (h : G)}) ∧
      (I.Nonempty → Set.ncard I = Nat.card (U ⊓ V : Subgroup G))

end MathlibPlus.Open.GroupTheory.Claim55342
