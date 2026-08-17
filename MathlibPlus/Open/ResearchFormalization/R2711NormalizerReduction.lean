import MathlibPlus.Open.ResearchFormalizationBatch01_01a000fa

namespace MathlibPlus.Open.ResearchFormalization.R2711

open MathlibPlus.Open.ResearchFormalizationBatch01_01a000fa

/-- Claim 42357: the right-regular normalizer reduction for the exact
`C₄ × C₃³` carrier supplied by the reviewed block-lift declaration. -/
def claim42357 : Prop :=
  let G := BlockGroup 3
  let R : Set (Equiv.Perm G) := rightRegular G
  let N : Subgroup (Equiv.Perm G) := Subgroup.normalizer R
  (Fintype.card G = 108) ∧
    Nat.card {a : G ≃+ G // a 0 = 0} = 22464 ∧
    (∀ p : Equiv.Perm G,
      p ∈ N ↔
        ∃ (g : G) (a : G ≃+ G),
          p = Equiv.addRight g * a.toEquiv) ∧
    Nat.card N = 108 * 22464 ∧
    (∀ f : Equiv.Perm G, f 0 = 0 →
      (∀ c : Equiv.Perm G,
        conjugateSet c R = conjugateSet f R →
          ∃ n : N,
            c = (n : Equiv.Perm G) * f) ∧
      ∀ S : Set G,
        (∀ r : Equiv.Perm G, r ∈ R →
          ∀ x y : G,
            (r y - r x ∈ S ↔ y - x ∈ S)) →
        (∀ t : Equiv.Perm G, t ∈ conjugateSet f R →
          ∀ x y : G,
            (t y - t x ∈ S ↔ y - x ∈ S)) →
        ((∃ c : Equiv.Perm G,
            (∀ x y : G, c y - c x ∈ S ↔ y - x ∈ S) ∧
              conjugateSet c R = conjugateSet f R) ↔
          ∃ a : {a : G ≃+ G // a 0 = 0},
            a.1 '' (f '' S) = S))

end MathlibPlus.Open.ResearchFormalization.R2711
