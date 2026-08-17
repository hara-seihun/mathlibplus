import Mathlib

open Set

namespace MathlibPlus.Open.ResearchFormalization.O0355Claim15626

noncomputable section

abbrev MultiIndex := Fin 5 →₀ ℕ

/-- The indices which can carry a nonzero cyclotomic exponent. -/
def supportedIndex (n : MultiIndex) : Prop :=
  1 ≤ n 0 ∧ 1 ≤ ∑ j : Fin 4, n j.succ

def primaryIndex (n : MultiIndex) : Prop :=
  ∃ j : Fin 4,
    n = Finsupp.single (0 : Fin 5) 1 + Finsupp.single j.succ 1

def activeIndex (c : MultiIndex → ℤ) (n : MultiIndex) : Prop :=
  c n ≠ 0 ∧ supportedIndex n

/-- The four shifts in the fixed order `(η, conj η, ρ, conj ρ)`. -/
def quartetShift (α τ : ℝ) : Fin 4 → ℂ := fun j =>
  ![(α : ℂ) - (τ : ℂ) * Complex.I,
    starRingEnd ℂ ((α : ℂ) - (τ : ℂ) * Complex.I),
    1 - ((α : ℂ) - (τ : ℂ) * Complex.I),
    starRingEnd ℂ (1 - ((α : ℂ) - (τ : ℂ) * Complex.I))] j

def shiftedZetaArgument
    (α τ : ℝ) (s₀ : ℂ) (n : MultiIndex) : ℂ :=
  (n 0 : ℂ) * s₀ +
    ∑ j : Fin 4, (n j.succ : ℂ) * quartetShift α τ j

/-- Claim 15626: the supported nonprimary factors have an unconditional
`A_n(α) + i q_n τ` form, and all higher and ambient zeta collisions are
removed by one countable set of positive heights. -/
def claim15626 : Prop :=
  ∀ (α : ℝ), Irrational α → 0 < α → α < (1 : ℝ) / 2 →
    ∀ (c : MultiIndex → ℤ),
      (∀ n, c n ≠ 0 → supportedIndex n) →
      ∃ (A : MultiIndex → Fin 4 → ℝ)
        (q : MultiIndex → Fin 4 → ℤ) (E : Set ℝ),
        E.Countable ∧ E ⊆ Set.Ioi (0 : ℝ) ∧
          (∀ n, c n ≠ 0 → ¬ primaryIndex n →
            ∀ t : Fin 4,
              ((q n t = 0 →
                  0 < A n t ∧ A n t ≠ 1 ∧
                    riemannZeta (A n t : ℂ) ≠ 0) ∧
                (q n t ≠ 0 →
                  ∀ z : ℂ, riemannZeta z = 0 →
                    ∀ τ₁ τ₂ : ℝ,
                      0 < τ₁ → 0 < τ₂ →
                      shiftedZetaArgument α τ₁
                          (quartetShift α τ₁ t) n = z →
                      shiftedZetaArgument α τ₂
                          (quartetShift α τ₂ t) n = z →
                      τ₁ = τ₂)) ∧
              ∀ τ : ℝ, 0 < τ →
                shiftedZetaArgument α τ (quartetShift α τ t) n =
                  (A n t : ℂ) + (q n t : ℂ) * (τ : ℂ) * Complex.I) ∧
          (∀ t : Fin 4, ∀ z : ℂ, riemannZeta z = 0 →
            ∀ τ₁ τ₂ : ℝ,
              0 < τ₁ → 0 < τ₂ →
              quartetShift α τ₁ t = z →
              quartetShift α τ₂ t = z →
              τ₁ = τ₂) ∧
          ∀ τ : ℝ, 0 < τ → τ ∉ E →
            riemannZeta (quartetShift α τ (0 : Fin 4)) ≠ 0 ∧
            riemannZeta (quartetShift α τ (1 : Fin 4)) ≠ 0 ∧
            riemannZeta (quartetShift α τ (2 : Fin 4)) ≠ 0 ∧
            riemannZeta (quartetShift α τ (3 : Fin 4)) ≠ 0 ∧
            ∀ n, c n ≠ 0 → ¬ primaryIndex n →
              ∀ t : Fin 4,
                riemannZeta
                    (shiftedZetaArgument α τ
                      (quartetShift α τ t) n) ≠ 0

end

end MathlibPlus.Open.ResearchFormalization.O0355Claim15626
