import Mathlib

namespace MathlibPlus.Algebra.Claim15400

/-- A polynomial has exact multiplicity `m` at `ρ` when the translated monomial
of order `m` divides it but the next one does not. -/
def HasExactRootMultiplicity {R : Type*} [CommRing R]
    (p : Polynomial R) (ρ : R) (m : ℕ) : Prop :=
  (Polynomial.X - Polynomial.C ρ) ^ m ∣ p ∧
    ¬ (Polynomial.X - Polynomial.C ρ) ^ (m + 1) ∣ p

/-- Divisibility by a factor with multiplicity `m` kills all lower evaluated
iterated derivatives at the marked point. -/
theorem lowerIteratedDerivativeEvalEqZero
    {R : Type*} [CommRing R] {Xi Y : Polynomial R} {ρ : R} {m : ℕ}
    (hXi : HasExactRootMultiplicity Xi ρ m) (hY : Xi ∣ Y) :
    ∀ k < m, ((Polynomial.derivative^[k]) Y).eval ρ = 0 := by
  intro k hk
  have hpow : (Polynomial.X - Polynomial.C ρ) ^ (m - k) ∣
      (Polynomial.derivative^[k]) Y := by
    apply Polynomial.pow_sub_dvd_iterate_derivative_of_pow_dvd k
    exact hXi.1.trans hY
  obtain ⟨Q, hQ⟩ := hpow
  rw [hQ, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_sub,
    Polynomial.eval_X, Polynomial.eval_C]
  simp [Nat.sub_ne_zero_of_lt hk]

end MathlibPlus.Algebra.Claim15400
