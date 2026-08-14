import Mathlib

namespace MathlibPlus.Open.Frontier

/-- Fixed-level fibers are bounded exactly when distinct coordinates receive distinct levels. -/
def fixedLevelFiberTheorem : Prop :=
  (∀ {α : Type*} (Q : Finset α) (k : ℕ)
      (queryLevel : Q → Fin k),
      Function.Injective queryLevel → Q.card ≤ k)
  ∧ (∀ k : ℕ,
      ∃ queryLevel : Fin k → Fin k,
        queryLevel = id ∧
        Function.Injective queryLevel ∧
        Fintype.card (Fin k) = k)
  ∧ (∀ (k : ℕ), ∀ hk : 0 < k,
      (∀ (N : ℕ),
        ∃ queryLevel : Fin N → Fin k,
          ∀ q : Fin N, queryLevel q = ⟨0, hk⟩) ∧
      (∀ (B : ℕ),
        ∃ (N : ℕ) (queryLevel : Fin N → Fin k),
          B < Fintype.card (Fin N) ∧
          ∀ q : Fin N, queryLevel q = ⟨0, hk⟩))

end MathlibPlus.Open.Frontier
