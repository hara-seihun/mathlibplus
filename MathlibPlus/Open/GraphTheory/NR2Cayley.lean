import Mathlib

namespace MathlibPlus.Open.GraphTheory

/-- Claim 32027: every finite simple undirected Cayley graph on
`C_p × S₃` is CI for every prime `p ≥ 7`; the statement is deliberately
undirected and quantifies arbitrary connection sets and presentation maps. -/
def claim32027_primeTimesSymmetricThreeUndirectedCI : Prop :=
  ∀ (p : ℕ), Nat.Prime p → 7 ≤ p →
    let G := Multiplicative (ZMod p) × Equiv.Perm (Fin 3)
    ∀ S T : Set G, 1 ∉ S → 1 ∉ T →
      (∀ x : G, x⁻¹ ∈ S ↔ x ∈ S) →
      (∀ x : G, x⁻¹ ∈ T ↔ x ∈ T) →
      ∀ e : G ≃ G,
        (∀ x y : G, x⁻¹ * y ∈ S ↔ (e x)⁻¹ * e y ∈ T) →
        ∃ α : G ≃* G, ∀ x : G, x ∈ S ↔ α x ∈ T

end MathlibPlus.Open.GraphTheory
