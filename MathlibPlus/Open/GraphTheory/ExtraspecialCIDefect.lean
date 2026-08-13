import Mathlib

namespace MathlibPlus.Open.GraphTheory

/-- Every finite extraspecial prime group other than the quaternion group of order eight
has an explicit disconnected ordinary Cayley CI defect.  Extraspeciality is expanded
using the center, commutator, and Frattini subgroups so that the registry node does not
depend on a new unchecked group-class definition. -/
def extraspecialPrimeGroupNonQuaternionCIDefect : Prop :=
  ∀ (p : ℕ) (G : Type) [Fintype G] [Group G],
    p.Prime →
    IsPGroup p G →
    Nat.card (Subgroup.center G) = p →
    commutator G = Subgroup.center G →
    frattini G = Subgroup.center G →
    (¬ Nonempty (G ≃* QuaternionGroup 2)) →
    ∃ S T : Set G,
      (1 : G) ∉ S ∧
      (1 : G) ∉ T ∧
      (∀ ⦃x : G⦄, x ∈ S → x⁻¹ ∈ S) ∧
      (∀ ⦃x : G⦄, x ∈ T → x⁻¹ ∈ T) ∧
      Set.ncard S = p - 1 ∧
      Set.ncard T = p - 1 ∧
      (∃ e : G ≃ G,
        e 1 = 1 ∧
        (∀ x y : G, x⁻¹ * y ∈ S ↔ (e x)⁻¹ * e y ∈ T)) ∧
      ¬ ∃ α : G ≃* G, α '' S = T

end MathlibPlus.Open.GraphTheory
