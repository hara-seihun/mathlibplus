import Mathlib

namespace MathlibPlus.Open.GroupTheory

/-- The admitted CI assertion for the stated elementary abelian-by-cyclic group. -/
def cayleyCI_c2Pow_r_times_c9 : Prop :=
  ∀ (r : ℕ),
    2 ≤ r →
      ∀ (x y : Fin r → ZMod 2) (c : ZMod 9),
        LinearIndependent (ZMod 2) ![x, y] →
          addOrderOf c = 3 →
            let G := (Fin r → ZMod 2) × ZMod 9
            let S : Set G := {(x, 0), (y, 0), (0, c), (0, -c)}
            S ⊆ ({0} : Set G)ᶜ ∧
              ∀ T : Set G,
                T ⊆ ({0} : Set G)ᶜ →
                  (∀ t ∈ T, -t ∈ T) →
                    (SimpleGraph.fromRel
                        (fun u v : G => ∃ s ∈ S, v = u + s) ≃g
                      SimpleGraph.fromRel
                        (fun u v : G => ∃ t ∈ T, v = u + t)) →
                      ∃ α : G ≃+ G, α '' S = T

/-- The admitted CI assertion for the two stated valencies in C₇ × Q₁₂. -/
def cayleyCI_c7_times_q12 : Prop :=
  let G := Multiplicative (ZMod 7) × QuaternionGroup 3
  ∀ S T : Set G,
    S ⊆ ({1} : Set G)ᶜ →
      T ⊆ ({1} : Set G)ᶜ →
        (∀ s ∈ S, s⁻¹ ∈ S) →
          (∀ t ∈ T, t⁻¹ ∈ T) →
            ((S.ncard = 8 ∧ T.ncard = 8) ∨
              (S.ncard = 75 ∧ T.ncard = 75)) →
              (SimpleGraph.fromRel
                  (fun u v : G => ∃ s ∈ S, v = u * s) ≃g
                SimpleGraph.fromRel
                  (fun u v : G => ∃ t ∈ T, v = u * t)) →
                ∃ α : G ≃* G, α '' S = T

end MathlibPlus.Open.GroupTheory
