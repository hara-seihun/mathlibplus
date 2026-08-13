import Mathlib

namespace MathlibPlus.Open.Analysis

/-- Faithful polynomial-interface registry node for completed-carrier
outside-context separation.  The carrier maps and the component-polynomial
interpretation are left as explicit source interfaces. -/
def completedCarrierOutsideContextSeparation_claim48020 : Prop :=
  ∀ {α : Type*} [CommRing α] [NoZeroDivisors α] [Nontrivial α]
    (a : ℕ) (P : Polynomial α) (Context : Type*)
    (R : Context → Polynomial α)
    (J : Context → Polynomial α → Polynomial α)
    (C D : Context),
    P ≠ 0 →
    P.coeff 0 = 0 →
    P.coeff a ≠ 0 →
    P.natDegree = a →
    (J C P = J D P ↔ R C = R D) ∧
    (R C - R D ≠ 0 →
      (R C - R D).natDegree < a →
      (J C P - J D P).coeff (a + (R C - R D).natDegree) =
        (R C - R D).coeff (R C - R D).natDegree * P.coeff a ∧
      (J C P - J D P).coeff (a + (R C - R D).natDegree) ≠ 0)

end MathlibPlus.Open.Analysis
