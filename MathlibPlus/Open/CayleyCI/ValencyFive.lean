import Mathlib

namespace MathlibPlus.Open.CayleyCI

/-- Claim 60198: the cardinality-five CI slice for the indicated finite abelian groups. -/
def valency_five_ci_for_c2_power_mul_c9 : Prop :=
  ∀ r : ℕ, (r = 3 ∨ r = 4 ∨ r = 5) →
    let G := (Fin r → ZMod 2) × ZMod 9
    ∀ S T : Finset G,
      0 ∉ S →
      (∀ x ∈ S, -x ∈ S) →
      S.card = 5 →
      0 ∉ T →
      (∀ x ∈ T, -x ∈ T) →
      (∃ e : G ≃ G,
        ∀ x y : G,
          (x ≠ y ∧ x - y ∈ S) ↔
            (e x ≠ e y ∧ e x - e y ∈ T)) →
      ∃ φ : G ≃+ G, ∀ x : G, x ∈ S ↔ φ x ∈ T

end MathlibPlus.Open.CayleyCI
