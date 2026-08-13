import Mathlib

namespace MathlibPlus.Open.GraphTheory

/-- Every finite normal extension of the cyclic group of order nine has a
connected directed Cayley CI defect.  The exact left-translation periods of the
pulled-back connection sets recover the chosen normal kernel. -/
def cyclicNineNormalQuotientConnectedDirectedCIDefect : Prop :=
  ∀ (G : Type) [Fintype G] [Group G] (N : Subgroup G) [N.Normal],
    Nonempty ((G ⧸ N) ≃* Multiplicative (ZMod 9)) →
    ∃ (S T : Set G) (e : G ≃ G),
      (1 : G) ∉ S ∧
      (1 : G) ∉ T ∧
      Set.ncard S = 4 * Nat.card N ∧
      Set.ncard T = 4 * Nat.card N ∧
      Subgroup.closure S = ⊤ ∧
      Subgroup.closure T = ⊤ ∧
      (∀ g : G, (fun x : G => g * x) '' S = S ↔ g ∈ N) ∧
      (∀ g : G, (fun x : G => g * x) '' T = T ↔ g ∈ N) ∧
      e 1 = 1 ∧
      Function.Involutive e ∧
      (∀ x y : G, x⁻¹ * y ∈ S ↔ (e x)⁻¹ * e y ∈ T) ∧
      ¬ ∃ α : G ≃* G, α '' S = T

end MathlibPlus.Open.GraphTheory
