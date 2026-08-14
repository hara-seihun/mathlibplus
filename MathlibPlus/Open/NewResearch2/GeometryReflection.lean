import Mathlib

namespace MathlibPlus.Open.NewResearch2.GeometryReflection

/-- Claim 19143: reversal of a rank-n jet has an endpoint at rank n+1, so
reflection is not an endomorphism of the same `Fin (n+1)` state space. -/
def claim19143 : Prop :=
  ∀ (R : Type*) [Ring R] (n : ℕ) (a : ℕ → R),
    let jet : Fin (n + 1) → R := fun i => a i.1
    let reflected : Fin (n + 2) → R := fun i => a (n + 1 - i.1)
    (reflected ⟨0, Nat.zero_lt_succ (n + 1)⟩ = a (n + 1)) ∧
      (∀ i : Fin (n + 1),
        reflected ⟨i.1 + 1, Nat.succ_lt_succ i.isLt⟩ =
          jet ⟨n - i.1, by omega⟩) ∧
      ¬ Nonempty (Fin (n + 2) ≃ Fin (n + 1))

end MathlibPlus.Open.NewResearch2.GeometryReflection
