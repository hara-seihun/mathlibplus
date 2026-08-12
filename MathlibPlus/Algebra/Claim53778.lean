import MathlibPlus.Basic

namespace MathlibPlus.Algebra.Claim53778

/-- In a characteristic-zero domain, a vanishing partial derivative of a
multivariate polynomial means that the polynomial has no dependence on that
variable.  Independence is expressed by exclusion from `MvPolynomial.vars`. -/
theorem pderiv_eq_zero_implies_not_mem_vars
    {K : Type*} [CommRing K] [NoZeroDivisors K] [CharZero K]
    {σ : Type*} (i : σ) (Δ : MvPolynomial σ K)
    (hΔ : MvPolynomial.pderiv i Δ = 0) : i ∉ Δ.vars := by
  classical
  intro hi
  obtain ⟨d, hd, hdi⟩ := (MvPolynomial.mem_vars_iff_mem_support i).mp hi
  have hcoeff : MvPolynomial.coeff d Δ ≠ 0 :=
    MvPolynomial.mem_support_iff.mp hd
  let m : σ →₀ ℕ := d - Finsupp.single i 1
  have hadd : m + Finsupp.single i 1 = d := by
    ext j
    by_cases hj : j = i
    · subst j
      have hone : (Finsupp.single i 1) i ≤ d i := by
        simpa using (Nat.one_le_iff_ne_zero.mpr
          (Finsupp.mem_support_iff.mp hdi))
      exact Nat.sub_add_cancel hone
    · simp [m, Finsupp.single_eq_of_ne hj]
  have hcast : ((m i : K) + 1) ≠ 0 := by
    simpa [Nat.cast_add] using
      (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero (m i)) :
        ((m i + 1 : ℕ) : K) ≠ 0)
  have hcoeffderiv : MvPolynomial.coeff m (MvPolynomial.pderiv i Δ) = 0 := by
    rw [hΔ]
    simp
  rw [MvPolynomial.coeff_pderiv] at hcoeffderiv
  have hcoeffderiv' : MvPolynomial.coeff d Δ * ((m i : K) + 1) = 0 := by
    simpa [hadd] using hcoeffderiv
  exact (mul_ne_zero hcoeff hcast) hcoeffderiv'

end MathlibPlus.Algebra.Claim53778
