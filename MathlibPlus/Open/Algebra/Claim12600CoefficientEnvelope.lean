import Mathlib

namespace MathlibPlus.Open.Algebra

/-- The coefficient-root envelope on real polynomials. -/
noncomputable def coefficientRootEnvelope_12600 (P : Polynomial ℝ) : ℝ :=
  max 1 (sSup (Set.range (fun n : {n : ℕ // 1 ≤ n} =>
    Real.rpow |P.coeff n.1| (1 / (n.1 : ℝ)))))

/-- The repeated outside-unit node coefficient identity and envelope bound. -/
def repeatedOutsideUnitNodeCoefficientLowerBound_12600 : Prop :=
  ∀ (r : ℝ) (N q_N : ℕ),
    1 < r →
    0 < q_N →
    let Δ_N : Polynomial ℝ :=
      Polynomial.X ^ q_N * (Polynomial.X - Polynomial.C r) ^ N
    Δ_N.coeff q_N = (-r) ^ N ∧
      coefficientRootEnvelope_12600 (1 + Δ_N) ≥
        Real.rpow r ((N : ℝ) / (q_N : ℝ))

end MathlibPlus.Open.Algebra
