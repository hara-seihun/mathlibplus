import MathlibPlus.Basic

open scoped ComplexConjugate

universe u v

namespace MathlibPlus.Algebra.Claim8047

/-- A conjugate pair selected with the same multiplicity has unit phase on the unit circle. -/
theorem conjugatePairPhase_eq_one (ω : ℂ) (r n : ℕ) (hω : ‖ω‖ = 1) :
    ω ^ (r * n) * (conj ω) ^ (r * n) = 1 := by
  rw [← map_pow]
  have hpow : ‖ω ^ (r * n)‖ = 1 := by
    rw [norm_pow, hω]
    simp
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hpow]
  norm_num

end MathlibPlus.Algebra.Claim8047

namespace MathlibPlus.Algebra.Claim15332

/-- The off-axis conjugate-pair quartic has the displayed real expansion. -/
theorem E_off_eq_expanded (a b : ℝ) (z : ℂ)
    (_ha0 : 0 < a) (_ha : a < 1 / 2) (_hb : 0 < b) :
    (z ^ 2 - ((a : ℂ) + (b : ℂ) * Complex.I) ^ 2) *
        (z ^ 2 - ((a : ℂ) - (b : ℂ) * Complex.I) ^ 2) =
      (z ^ 2 - (a : ℂ) ^ 2 + (b : ℂ) ^ 2) ^ 2 +
        4 * (a : ℂ) ^ 2 * (b : ℂ) ^ 2 := by
  ring_nf
  simp

/-- The line and off-axis quartic formulas are even in the polynomial variable. -/
theorem E_line_even (a b : ℝ) (z : ℂ)
    (_ha0 : 0 < a) (_ha : a < 1 / 2) (_hb : 0 < b) :
    ((-z) ^ 2 + (b : ℂ) ^ 2) ^ 2 = (z ^ 2 + (b : ℂ) ^ 2) ^ 2 := by
  ring

theorem E_off_even (a b : ℝ) (z : ℂ)
    (_ha0 : 0 < a) (_ha : a < 1 / 2) (_hb : 0 < b) :
    (((-z) ^ 2 - ((a : ℂ) + (b : ℂ) * Complex.I) ^ 2) *
        ((-z) ^ 2 - ((a : ℂ) - (b : ℂ) * Complex.I) ^ 2)) =
      ((z ^ 2 - ((a : ℂ) + (b : ℂ) * Complex.I) ^ 2) *
        (z ^ 2 - ((a : ℂ) - (b : ℂ) * Complex.I) ^ 2)) := by
  ring

end MathlibPlus.Algebra.Claim15332

namespace MathlibPlus.Algebra.Claim8598

/-- Finite unweighted source telescoping identity, with the local source term
written as its displayed difference-plus-error expression. -/
theorem unweightedSourceTelescoping (U E : ℕ → ℚ) {A B : ℕ} (hAB : A ≤ B) :
    (∑ k ∈ Finset.Icc A B, (U k - U (k + 1) + E k) / 2) =
      (U A - U (B + 1)) / 2 +
        (∑ k ∈ Finset.Icc A B, E k) / 2 := by
  induction B, hAB using Nat.le_induction with
  | base =>
      simp
      ring
  | succ B hAB ih =>
      rw [Finset.sum_Icc_succ_top (by omega)]
      rw [ih]
      rw [Finset.sum_Icc_succ_top (by omega)]
      ring

end MathlibPlus.Algebra.Claim8598

namespace MathlibPlus.LinearAlgebra.Claim4985

/-- Rank of a nested row family is monotone because adding rows enlarges its
linear span. -/
theorem rank_profile_monotone
    {K : Type u} {V : Type v} [DivisionRing K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (M : ℕ → Set V)
    (hM : ∀ {q1 q2 : ℕ}, q1 ≤ q2 → M q1 ⊆ M q2) :
    Monotone (fun q => Module.finrank K (Submodule.span K (M q))) := by
  intro q1 q2 hq
  exact Set.finrank_mono (hM hq)

end MathlibPlus.LinearAlgebra.Claim4985
