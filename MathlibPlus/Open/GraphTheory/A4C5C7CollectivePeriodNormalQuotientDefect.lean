import Mathlib

namespace MathlibPlus.Open.GraphTheory

/-- Every finite normal extension of `A₄ × C₅ × C₇` has a marker-free
simultaneous two-relation directed Cayley CI defect.  Neither coordinate alone
recovers the kernel: their translation-period subgroups have relative orders
five and seven, while their intersection is exactly the kernel. -/
def alternatingFourCyclicFiveSevenCollectivePeriodNormalQuotientDefect : Prop :=
  ∀ (G : Type) [Fintype G] [Group G] (N : Subgroup G) [N.Normal],
    Nonempty ((G ⧸ N) ≃*
      (alternatingGroup (Fin 4) ×
        (Multiplicative (ZMod 5) × Multiplicative (ZMod 7)))) →
    ∃ (S T : Fin 2 → Set G) (e : G ≃ G),
      (∀ i, (1 : G) ∉ S i) ∧
      (∀ i, (1 : G) ∉ T i) ∧
      Set.ncard (S 0) = 5 * Nat.card N ∧
      Set.ncard (T 0) = 5 * Nat.card N ∧
      Set.ncard (S 1) = 35 * Nat.card N ∧
      Set.ncard (T 1) = 35 * Nat.card N ∧
      Set.ncard {g : G | (fun x : G => g * x) '' S 0 = S 0} =
        5 * Nat.card N ∧
      Set.ncard {g : G | (fun x : G => g * x) '' T 0 = T 0} =
        5 * Nat.card N ∧
      Set.ncard {g : G | (fun x : G => g * x) '' S 1 = S 1} =
        7 * Nat.card N ∧
      Set.ncard {g : G | (fun x : G => g * x) '' T 1 = T 1} =
        7 * Nat.card N ∧
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
