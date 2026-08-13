import Mathlib

namespace MathlibPlus.Open.GraphTheory

/-- Every finite extraspecial group at an odd prime has an ordinary undirected
Cayley CI defect of the least possible positive valency, namely two. -/
def extraspecialOddPrimeGroupSharpValencyTwoCIDefect : Prop :=
  ∀ (p : ℕ) (G : Type) [Fintype G] [Group G],
    p.Prime →
    p ≠ 2 →
    IsPGroup p G →
    Nat.card (Subgroup.center G) = p →
    commutator G = Subgroup.center G →
    frattini G = Subgroup.center G →
    (∃ S T : Set G,
      (1 : G) ∉ S ∧
      (1 : G) ∉ T ∧
      (∀ ⦃x : G⦄, x ∈ S → x⁻¹ ∈ S) ∧
      (∀ ⦃x : G⦄, x ∈ T → x⁻¹ ∈ T) ∧
      Set.ncard S = 2 ∧
      Set.ncard T = 2 ∧
      Subgroup.closure S = Subgroup.center G ∧
      Nat.card (Subgroup.closure T) = p ∧
      Subgroup.closure T ≠ Subgroup.center G ∧
      (∃ e : G ≃ G,
        e 1 = 1 ∧
        (∀ x y : G, x⁻¹ * y ∈ S ↔ (e x)⁻¹ * e y ∈ T)) ∧
      ¬ ∃ α : G ≃* G, α '' S = T) ∧
    (∀ U : Set G,
      (1 : G) ∉ U →
      (∀ ⦃x : G⦄, x ∈ U → x⁻¹ ∈ U) →
      Set.ncard U ≠ 1)

end MathlibPlus.Open.GraphTheory
