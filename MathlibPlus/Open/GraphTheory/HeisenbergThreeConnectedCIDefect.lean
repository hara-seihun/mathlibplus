import Mathlib

namespace MathlibPlus.Open.GraphTheory

/-- The exponent-three extraspecial group of order twenty-seven has connected
ordinary Cayley CI-defect valency exactly twenty.  The group is specified by
its structural invariants, avoiding a new presentation definition in the open
registry. -/
def heisenbergThreeSharpConnectedCIDefectValency : Prop :=
  ∀ (G : Type) [Fintype G] [Group G],
    IsPGroup 3 G →
    Nat.card G = 27 →
    Nat.card (Subgroup.center G) = 3 →
    commutator G = Subgroup.center G →
    frattini G = Subgroup.center G →
    (∀ x : G, x ^ (3 : ℕ) = 1) →
    (∃ S T : Set G,
      (1 : G) ∉ S ∧
      (1 : G) ∉ T ∧
      (∀ ⦃x : G⦄, x ∈ S → x⁻¹ ∈ S) ∧
      (∀ ⦃x : G⦄, x ∈ T → x⁻¹ ∈ T) ∧
      Set.ncard S = 20 ∧
      Set.ncard T = 20 ∧
      Subgroup.closure S = ⊤ ∧
      Subgroup.closure T = ⊤ ∧
      (∃ e : G ≃ G,
        e 1 = 1 ∧
        ∀ x y : G, x⁻¹ * y ∈ S ↔ (e x)⁻¹ * e y ∈ T) ∧
      ¬ ∃ α : G ≃* G, α '' S = T) ∧
    ∀ S T : Set G,
      (1 : G) ∉ S →
      (1 : G) ∉ T →
      (∀ ⦃x : G⦄, x ∈ S → x⁻¹ ∈ S) →
      (∀ ⦃x : G⦄, x ∈ T → x⁻¹ ∈ T) →
      Subgroup.closure S = ⊤ →
      Subgroup.closure T = ⊤ →
      Set.ncard S < 20 →
      Set.ncard T < 20 →
      (∃ e : G ≃ G,
        ∀ x y : G, x⁻¹ * y ∈ S ↔ (e x)⁻¹ * e y ∈ T) →
      ∃ α : G ≃* G, α '' S = T

end MathlibPlus.Open.GraphTheory
