import Mathlib

namespace MathlibPlus.Open.GraphTheory

/-- For every prime `p ≥ 5`, every finite normal extension of `A₄ × C_p²`
has a marker-free simultaneous two-relation directed Cayley CI defect whose two
coordinate period groups have the same nontrivial relative order `p` and recover
the kernel only through their transverse intersection. -/
def alternatingFourPrimePlaneTransversePeriodNormalQuotientDefect : Prop :=
  ∀ (p : ℕ), p.Prime → 5 ≤ p →
  ∀ (G : Type) [Fintype G] [Group G] (N : Subgroup G) [N.Normal],
    Nonempty ((G ⧸ N) ≃*
      (alternatingGroup (Fin 4) ×
        Multiplicative (ZMod p × ZMod p))) →
    ∃ (S T : Fin 2 → Set G) (e : G ≃ G),
      (∀ i, (1 : G) ∉ S i) ∧
      (∀ i, (1 : G) ∉ T i) ∧
      Set.ncard (S 0) = p * Nat.card N ∧
      Set.ncard (T 0) = p * Nat.card N ∧
      Set.ncard (S 1) = 5 * p * Nat.card N ∧
      Set.ncard (T 1) = 5 * p * Nat.card N ∧
      Set.ncard {g : G | (fun x : G => g * x) '' S 0 = S 0} =
        p * Nat.card N ∧
      Set.ncard {g : G | (fun x : G => g * x) '' T 0 = T 0} =
        p * Nat.card N ∧
      Set.ncard {g : G | (fun x : G => g * x) '' S 1 = S 1} =
        p * Nat.card N ∧
      Set.ncard {g : G | (fun x : G => g * x) '' T 1 = T 1} =
        p * Nat.card N ∧
      (∀ g : G,
        ((fun x : G => g * x) '' S 0 = S 0 ∧
          (fun x : G => g * x) '' S 1 = S 1) ↔ g ∈ N) ∧
      (∀ g : G,
        ((fun x : G => g * x) '' T 0 = T 0 ∧
          (fun x : G => g * x) '' T 1 = T 1) ↔ g ∈ N) ∧
      Subgroup.closure (S 0 ∪ S 1) = ⊤ ∧
      Subgroup.closure (T 0 ∪ T 1) = ⊤ ∧
      e 1 = 1 ∧
      Function.Involutive e ∧
      (∀ i x y, x⁻¹ * y ∈ S i ↔ (e x)⁻¹ * e y ∈ T i) ∧
      ¬ ∃ α : G ≃* G, ∀ i, α '' S i = T i

end MathlibPlus.Open.GraphTheory
