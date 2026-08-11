import Mathlib

namespace MathlibPlus.Analysis

/-- The complex-variable factorization and zero-normalization asserted in
admitted claim 19028.  The infinite product is indexed by the positive
natural numbers, exactly as in its source notation. -/
theorem normalizedDensityMatchedInfiniteProduct_claim19028 :
    (∀ n : {n : ℕ // 1 ≤ n}, ∀ z : ℂ,
      let q : ℝ := Real.exp (-(n.1 : ℝ) ^ 2)
      let ell : ℝ := Real.pi / (n.1 : ℝ)
      (1 + 2 * (q : ℂ) * Complex.cosh ((ell : ℂ) * z) + (q : ℂ) ^ 2) /
          (1 + (q : ℂ)) ^ 2 =
        ((1 + (q : ℂ) * Complex.exp ((ell : ℂ) * z)) *
          (1 + (q : ℂ) * Complex.exp (-((ell : ℂ) * z)))) /
          (1 + (q : ℂ)) ^ 2) ∧
    (let F : ℂ → ℂ := fun z =>
      ∏' n : {n : ℕ // 1 ≤ n},
        let q : ℝ := Real.exp (-(n.1 : ℝ) ^ 2)
        let ell : ℝ := Real.pi / (n.1 : ℝ)
        (1 + 2 * (q : ℂ) * Complex.cosh ((ell : ℂ) * z) + (q : ℂ) ^ 2) /
            (1 + (q : ℂ)) ^ 2
     F 0 = 1) := by
  constructor
  · intro n z
    dsimp
    let q : ℂ := (Real.exp (-(n.1 : ℝ) ^ 2) : ℂ)
    let x : ℂ := (Real.pi / (n.1 : ℝ) : ℂ) * z
    have hexp : Complex.exp x * Complex.exp (-x) = 1 := by
      rw [← Complex.exp_add]
      simp
    have hidentity :
        (1 + 2 * q * Complex.cosh x + q ^ 2) / (1 + q) ^ 2 =
          ((1 + q * Complex.exp x) * (1 + q * Complex.exp (-x))) /
            (1 + q) ^ 2 := by
      rw [show Complex.cosh x =
        (Complex.exp x + Complex.exp (-x)) / 2 by rfl]
      have hnum : 1 + q * (Complex.exp x + Complex.exp (-x)) + q ^ 2 =
          (1 + q * Complex.exp x) * (1 + q * Complex.exp (-x)) := by
        linear_combination -(q ^ 2) * hexp
      rw [show 2 * q * ((Complex.exp x + Complex.exp (-x)) / 2) =
          q * (Complex.exp x + Complex.exp (-x)) by ring]
      rw [hnum]
    simpa [q, x] using hidentity
  · dsimp
    have hfun :
        (fun n : {n : ℕ // 1 ≤ n} =>
          (1 + 2 * (Real.exp (-(n.1 : ℝ) ^ 2) : ℂ) * Complex.cosh
            (((Real.pi / (n.1 : ℝ) : ℝ) : ℂ) * 0) +
            (Real.exp (-(n.1 : ℝ) ^ 2) : ℂ) ^ 2) /
              (1 + (Real.exp (-(n.1 : ℝ) ^ 2) : ℂ)) ^ 2) =
        (fun _ => (1 : ℂ)) := by
      funext n
      let q : ℂ := (Real.exp (-(n.1 : ℝ) ^ 2) : ℂ)
      have hq : (1 + q) ^ 2 ≠ 0 := by
        apply pow_ne_zero
        intro h
        have hr := congrArg Complex.re h
        dsimp [q] at hr
        have hqpos : 0 < Real.exp (-(n.1 : ℝ) ^ 2) := by positivity
        linarith
      have hz : ((Real.pi / (n.1 : ℝ) : ℝ) : ℂ) * 0 = 0 := by simp
      change (1 + 2 * q * Complex.cosh (((Real.pi / (n.1 : ℝ) : ℝ) : ℂ) * 0) + q ^ 2) /
        (1 + q) ^ 2 = 1
      apply (div_eq_iff hq).2
      rw [hz, Complex.cosh_zero]
      ring
    rw [hfun]
    simp

end MathlibPlus.Analysis
