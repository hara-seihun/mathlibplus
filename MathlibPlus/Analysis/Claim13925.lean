import Mathlib

namespace MathlibPlus.Analysis.Claim13925

/-- A normalized positive-definite function on the additive real group is
bounded by one.  Positive definiteness is written in its finite quadratic-form
form, so the full finite-list quantifier is retained. -/
theorem normalized_positive_definite_bound_claim13925
    (a : ℝ → ℂ)
    (hpd : ∀ (n : ℕ) (x : Fin n → ℝ) (c : Fin n → ℂ),
      ∃ r : ℝ, 0 ≤ r ∧
        (∑ i : Fin n, ∑ j : Fin n,
          star (c i) * a (x i - x j) * c j) = r)
    (ha0 : a 0 = 1) :
    ∀ x : ℝ, ‖a x‖ ≤ 1 := by
  intro x
  have hconj : a (-x) = star (a x) := by
    obtain ⟨r₁, hr₁, hq₁⟩ := hpd 2 ![0, x] ![1, 1]
    obtain ⟨r₂, hr₂, hq₂⟩ := hpd 2 ![0, x] ![1, Complex.I]
    have him₁ := congrArg Complex.im hq₁
    have him₂ := congrArg Complex.im hq₂
    simp [Fin.sum_univ_two, ha0] at him₁ him₂
    apply Complex.ext
    · change (a (-x)).re = (a x).re
      linarith
    · change (a (-x)).im = -(a x).im
      linarith
  obtain ⟨r, hr, hq⟩ := hpd 2 ![0, x] ![-star (a x), 1]
  have hreal := congrArg Complex.re hq
  have himag := congrArg Complex.im hq
  simp [Fin.sum_univ_two, ha0, hconj] at hreal himag
  have hreal' : 1 - Complex.normSq (a x) = r := by
    rw [Complex.normSq_apply]
    linarith [hreal]
  have hnormSq : Complex.normSq (a x) ≤ 1 := by
    linarith [hreal', hr]
  have hnorm : ‖a x‖ ^ 2 ≤ 1 := by
    simpa [Complex.sq_norm] using hnormSq
  nlinarith [sq_nonneg (‖a x‖ - 1)]

end MathlibPlus.Analysis.Claim13925
