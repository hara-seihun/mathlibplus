import Mathlib

namespace MathlibPlus.Algebra.Claim58679

/--
The two-exponential shifted-trace identity from R-5646#S2.  A polynomial in
`z` is used after evaluating each coefficient `x_λ` in an arbitrary
commutative ring; `K.sum` is the resulting coefficientwise evaluation of
`Φ_s`.  The hypothesis on `x` is exactly the rank-two substitution
`x_j = α p^(j-1) + β q^(j-1)` for positive indices.
-/
theorem shiftedTraceTwoExponential
    {R : Type*} [CommRing R]
    (α β p q : R) (x : ℕ → R) (s : ℕ)
    (hs : 1 ≤ s)
    (hx : ∀ n : ℕ, 1 ≤ n →
      x n = α * p ^ (n - 1) + β * q ^ (n - 1))
    (K : Polynomial R) :
    K.sum (fun a c => c * x (a + s)) =
      α * p ^ (s - 1) * Polynomial.eval p K +
        β * q ^ (s - 1) * Polynomial.eval q K := by
  induction K using Polynomial.induction_on' with
  | add P Q hP hQ =>
      rw [Polynomial.sum_add_index]
      · simp only [Polynomial.eval_add]
        rw [hP, hQ]
        ring
      · intro i
        simp
      · intro i c₁ c₂
        ring
  | monomial n c =>
      rw [Polynomial.sum_monomial_index]
      · rw [Polynomial.eval_monomial, Polynomial.eval_monomial]
        have hns : 1 ≤ n + s := by
          omega
        rw [hx (n + s) hns]
        have hexp : n + s - 1 = n + (s - 1) := by
          omega
        rw [hexp, pow_add, pow_add]
        ring
      · simp

end MathlibPlus.Algebra.Claim58679
