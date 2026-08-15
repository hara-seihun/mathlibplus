import Mathlib

namespace MathlibPlus.Open.Analysis

/--
For an integral base `q ≥ 2`, the root forced at `r² = q⁻¹` is the
central preimage of `s = 1`; after the zeta pole is cancelled, its
simple-root condition is detected by the nonvanishing central value of
the regularized product `F_P`.
-/
def commensuratePolynomialMultiplierForcedRoot : Prop :=
  ∀ (q : ℕ), 2 ≤ q →
    ∀ (P : Polynomial ℂ), P ≠ 0 →
      let qC : ℂ := (q : ℂ)
      let r : ℂ := Complex.exp (-((1 : ℂ) / 2) * Complex.log qC)
      let qpow : ℂ → ℂ := fun s => Complex.exp (-s * Complex.log qC)
      let A : ℂ → ℂ := fun s => Polynomial.eval (qpow s) P
      let central : ℂ :=
        -(Complex.log qC) * (r ^ 2) * Polynomial.eval (r ^ 2) P.derivative
      let F : ℂ → ℂ := fun s =>
        if s = 1 then central else A s * riemannZeta s
      Polynomial.eval (r ^ 2) P = 0 →
        DifferentiableAt ℂ F 1 ∧
          (Polynomial.eval (r ^ 2) P.derivative ≠ 0 ↔ F 1 ≠ 0)

end MathlibPlus.Open.Analysis
