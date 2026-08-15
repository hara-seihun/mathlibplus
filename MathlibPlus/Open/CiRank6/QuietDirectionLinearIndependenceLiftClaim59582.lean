import Mathlib

namespace MathlibPlus.Open.CiRank6

/--
A linear correction extending a prescribed increment profile on quiet directions
exists exactly when the profile respects every finitely supported linear relation.
-/
def quietDirectionLinearIndependenceLiftClaim59582
    (K H D : Type*)
    [DivisionRing K]
    [AddCommGroup H] [Module K H]
    [AddCommGroup D] [Module K D]
    (Q : Set H) (κ : Q → D) : Prop :=
  ((∃ L : H →ₗ[K] D, ∀ h : Q, L h = κ h) ↔
      ∀ a : Q →₀ K,
        (∑ h ∈ a.support, a h • (h : H) = 0) →
          ∑ h ∈ a.support, a h • κ h = 0) ∧
    ((∀ a : Q →₀ K,
        (∑ h ∈ a.support, a h • (h : H) = 0) →
          ∑ h ∈ a.support, a h • κ h = 0) →
      ∃ L : H →ₗ[K] D,
        (∀ h : Q, L h = κ h) ∧
          ∀ x : H, ∀ h : Q,
            L (x + (h : H)) - L x = κ h) ∧
    (LinearIndependent K (fun h : Q => (h : H)) →
      ∀ κ' : Q → D,
        ∃ L : H →ₗ[K] D, ∀ h : Q, L h = κ' h) ∧
    (∀ m : ℕ, ∀ h : Fin m → Q,
      (∑ i : Fin m, (h i : H) = 0) →
        (∑ i : Fin m, κ (h i) ≠ 0) →
          ¬ ∃ c : H → D, ∀ x : H, ∀ q : Q,
              c (x + (q : H)) - c x = κ q)

end MathlibPlus.Open.CiRank6
