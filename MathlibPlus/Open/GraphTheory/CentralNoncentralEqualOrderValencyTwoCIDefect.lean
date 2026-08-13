import Mathlib

namespace MathlibPlus.Open.GraphTheory

/-- A central and a noncentral element of the same order at least three
produce a valency-two ordinary undirected Cayley-isomorphism defect. -/
def centralNoncentralEqualOrderValencyTwoCIDefect : Prop :=
  ∀ (G : Type*) [Finite G] [Group G],
    (∃ u v : G,
      u ∈ Subgroup.center G ∧
      v ∉ Subgroup.center G ∧
      3 ≤ orderOf u ∧
      orderOf u = orderOf v) →
    ∃ u v : G,
      u ∈ Subgroup.center G ∧
      v ∉ Subgroup.center G ∧
      3 ≤ orderOf u ∧
      orderOf u = orderOf v ∧
      let S : Set G := {u, u⁻¹}
      let T : Set G := {v, v⁻¹}
      S = S⁻¹ ∧
      T = T⁻¹ ∧
      (1 : G) ∉ S ∧
      (1 : G) ∉ T ∧
      S.ncard = 2 ∧
      T.ncard = 2 ∧
      (∃ e : G ≃ G,
        e 1 = 1 ∧
        (∀ x y, x⁻¹ * y ∈ S ↔ (e x)⁻¹ * e y ∈ T)) ∧
      ¬ ∃ φ : G ≃* G, φ '' S = T

end MathlibPlus.Open.GraphTheory
