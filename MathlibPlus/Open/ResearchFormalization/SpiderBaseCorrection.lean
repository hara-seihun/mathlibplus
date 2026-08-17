import MathlibPlus.Open.ResearchFormalize.SpiderIndependence

namespace MathlibPlus.Open.ResearchFormalization

/-- Claim 48188: the three-long-arm broom polynomial is a real-rooted base
with a correction supported only in ranks one through four, so the later
log-concavity slacks are inherited from the base. -/
def claim_48188 : Prop := by
  classical
  exact
    ∀ r : ℕ,
      let A : Polynomial ℚ :=
        (1 + Polynomial.X) ^ r *
          (1 + 3 * Polynomial.X + Polynomial.X ^ 2) ^ 3
      let C : Polynomial ℚ :=
        Polynomial.X * (1 + 2 * Polynomial.X) ^ 3
      let I : Polynomial ℚ := A + C
      let Areal : Polynomial ℝ := A.map (algebraMap ℚ ℝ)
      let q : Polynomial ℝ :=
        1 + 3 * Polynomial.X + Polynomial.X ^ 2
      (Polynomial.map (algebraMap ℤ ℚ)
          (MathlibPlus.Open.ResearchFormalizeBatch.spiderIndependencePolynomial r 3) = I) ∧
        (∀ z : ℂ,
          Polynomial.IsRoot (Areal.map Complex.ofRealHom) z →
            z.im = 0 ∧ z.re < 0) ∧
        (∀ z : ℝ,
          Polynomial.IsRoot q z ↔
            z = (-3 + Real.sqrt 5) / 2 ∨
              z = (-3 - Real.sqrt 5) / 2) ∧
        C = Polynomial.X + 6 * Polynomial.X ^ 2 +
          12 * Polynomial.X ^ 3 + 8 * Polynomial.X ^ 4 ∧
        (∀ k : ℕ, k = 0 ∨ 5 ≤ k → I.coeff k = A.coeff k) ∧
        (∀ k : ℕ, 6 ≤ k →
          0 ≤ A.coeff k ^ 2 - A.coeff (k - 1) * A.coeff (k + 1) ∧
          I.coeff k ^ 2 - I.coeff (k - 1) * I.coeff (k + 1) =
            A.coeff k ^ 2 - A.coeff (k - 1) * A.coeff (k + 1)) ∧
        (∀ k : ℕ, 1 ≤ k → k ≤ 5 →
          0 < I.coeff k ^ 2 - I.coeff (k - 1) * I.coeff (k + 1))

end MathlibPlus.Open.ResearchFormalization
