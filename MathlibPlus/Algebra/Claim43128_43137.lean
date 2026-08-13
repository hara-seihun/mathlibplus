import MathlibPlus.Basic

namespace MathlibPlus.Algebra.Claim43128_43137

/-!
The packet gives the slice recurrence but does not specify the ambient type of
its operators.  The recurrence consequence is therefore recorded over an
arbitrary commutative ring, with the slice values in that ring.
-/

/-- Claim 43128: the displayed first slice and recurrence have the stated closed form. -/
theorem sliceClosedForm
    {R : Type _} [CommRing R]
    (N T g : R) (f : ℕ → R)
    (h₁ : f 1 = (-N) * g)
    (hrec : ∀ m : ℕ, 2 ≤ m → f m = (-T) * f (m - 1)) :
    ∀ m : ℕ, 1 ≤ m → f m = (-1 : R) ^ m * T ^ (m - 1) * N * g := by
  intro m hm
  induction m with
  | zero => omega
  | succ m ih =>
      by_cases hzero : m = 0
      · subst m
        simpa using h₁
      · have hmpos : 1 ≤ m := by omega
        rw [hrec (m + 1) (by omega)]
        simp only [Nat.add_sub_cancel]
        rw [ih hmpos]
        rw [pow_succ]
        have hpow : T ^ m = T * T ^ (m - 1) := by
          rw [← pow_succ']
          congr 1
          omega
        rw [hpow]
        ring

/-!
The source's phrase "as polynomials in `a`" is made explicit by quantifying
that identity over every rational value of `a`.  The coefficient conclusion is
then proved without introducing any source-specific profile-ring definitions.
-/

/-- Claim 43137: coefficient comparison in the displayed rational polynomial identity. -/
theorem coefficientComparison
    (V₀ v₁ A₀ A₁ A₂ D₀ D₁ : ℚ)
    (hV₀ : V₀ ≠ 0)
    (h : ∀ a : ℚ,
      (V₀ + a * v₁) * (D₀ + a * D₁) =
        (A₀ + a * A₁ + a ^ 2 * A₂) ^ 2 + (V₀ + a * v₁) ^ 4 / 12) :
    v₁ = 0 ∧ A₂ = 0 ∧ A₁ = 0 ∧ D₁ = 0 := by
  have h0 := h 0
  have h1 := h 1
  have hm1 := h (-1)
  have h2 := h 2
  have hm2 := h (-2)
  ring_nf at h0 h1 hm1 h2 hm2
  have h4 : A₂ ^ 2 + v₁ ^ 4 / 12 = 0 := by
    linear_combination
      -(1 / 24 : ℚ) * hm2 + (1 / 6 : ℚ) * hm1 -
        (1 / 4 : ℚ) * h0 + (1 / 6 : ℚ) * h1 -
        (1 / 24 : ℚ) * h2
  have hA2sq : A₂ ^ 2 = 0 := by
    nlinarith [h4, sq_nonneg (v₁ ^ 2)]
  have hA2 : A₂ = 0 := sq_eq_zero_iff.mp hA2sq
  have hv14 : v₁ ^ 4 = 0 := by
    nlinarith [h4, hA2sq]
  have hv1 : v₁ = 0 :=
    (pow_eq_zero_iff (by norm_num : (4 : ℕ) ≠ 0)).mp hv14
  have h0' := h0
  have h1' := h1
  have hm1' := hm1
  rw [hv1, hA2] at h1' hm1'
  have hA1 : A₁ = 0 := by
    have hA1sq : A₁ ^ 2 = 0 := by
      linear_combination
        -(1 / 2 : ℚ) * h1' - (1 / 2 : ℚ) * hm1' + h0'
    exact sq_eq_zero_iff.mp hA1sq
  rw [hA1] at h1' hm1'
  have hVd : V₀ * D₁ = 0 := by
    linear_combination (1 / 2 : ℚ) * h1' - (1 / 2 : ℚ) * hm1'
  have hD1 : D₁ = 0 := (mul_eq_zero.mp hVd).resolve_left hV₀
  exact ⟨hv1, hA2, hA1, hD1⟩

end MathlibPlus.Algebra.Claim43128_43137
