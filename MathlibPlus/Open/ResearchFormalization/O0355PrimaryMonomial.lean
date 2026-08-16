import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization

/--
Claim 15625: for the irrational planted quartet, a nontrivial cyclotomic
multi-index can have shifted zeta argument `1` only at the reflected primary
monomial.  The `Fin 4` tuple is the displayed enumeration
`(η, conj η, ρ, conj ρ)` of the quartet.
-/
def irrationalityIsolatesPrimaryMonomial15625 : Prop :=
  ∀ (α τ : ℝ),
    Irrational α →
    0 < α →
    α < 1 / 2 →
    0 < τ →
    let η : ℂ := (α : ℂ) - (τ : ℂ) * Complex.I
    let ρ : ℂ := 1 - η
    let shifts : Fin 4 → ℂ :=
      ![η, (starRingEnd ℂ) η, ρ, (starRingEnd ℂ) ρ]
    let A : Set ℂ :=
      {η, (starRingEnd ℂ) η, ρ, (starRingEnd ℂ) ρ}
    ∀ (s₀ : ℂ),
      s₀ ∈ A →
      ∀ (n₀ : ℕ) (n : Fin 4 → ℕ),
        1 ≤ n₀ →
        1 ≤ ∑ j : Fin 4, n j →
        (n₀ : ℂ) * s₀ +
            ∑ j : Fin 4, (n j : ℂ) * shifts j = 1 →
          ∃! j : Fin 4,
            shifts j = 1 - s₀ ∧
              n₀ = 1 ∧
              n j = 1 ∧
              ∀ k : Fin 4, k ≠ j → n k = 0

end MathlibPlus.Open.ResearchFormalization
