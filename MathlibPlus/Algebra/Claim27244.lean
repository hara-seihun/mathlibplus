import MathlibPlus.Basic

namespace MathlibPlus.Algebra

/-- The irreducible-direction divisor core of claim 27244 in the original
multivariate rational polynomial ring. -/
theorem irreducibleDirectionDivisor_claim27244
    {σ : Type*} [DecidableEq σ]
    {V U Q : MvPolynomial σ ℚ} (hV : Irreducible V)
    (hfactor : V * U = Q ^ 2) :
    V ∣ Q := by
  have hdiv : V ∣ Q ^ 2 := by
    rw [← hfactor]
    exact dvd_mul_right V U
  exact hV.prime.dvd_of_dvd_pow hdiv

end MathlibPlus.Algebra
