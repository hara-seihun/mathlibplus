import Mathlib

namespace MathlibPlus.Open.Analysis

/--
A circular resolvent certificate from equally spaced samples of the smallest
singular value.  The contour is the positively oriented circle encoded by its
center and radius; its orientation does not affect the resolvent maximum.
-/
def finiteCircularResolventCertificate : Prop :=
  ∀ (r : ℕ), 0 < r →
    ∀ (N : ℕ), 0 < N →
      ∀ (Ahat : Matrix (Fin r) (Fin r) ℂ) (center : ℂ) (RΓ : ℝ),
        0 ≤ RΓ →
        let vectorNorm : (Fin r → ℂ) → ℝ := fun x =>
          Real.sqrt (∑ i : Fin r, ‖x i‖ ^ 2)
        let sigmaMin : Matrix (Fin r) (Fin r) ℂ → ℝ := fun M =>
          sInf {s : ℝ | ∃ x : Fin r → ℂ,
            vectorNorm x = 1 ∧ s = vectorNorm (M.mulVec x)}
        let operatorNorm2 : Matrix (Fin r) (Fin r) ℂ → ℝ := fun M =>
          sSup {s : ℝ | ∃ x : Fin r → ℂ,
            vectorNorm x = 1 ∧ s = vectorNorm (M.mulVec x)}
        let circle : Set ℂ := {z | ‖z - center‖ = RΓ}
        let samples : Fin N → ℂ := fun k =>
          center + (RΓ : ℂ) * Complex.exp
            (Complex.I * (2 * (Real.pi : ℂ) * (k.1 : ℂ) / (N : ℂ)))
        let sStar : ℝ :=
          sInf (Set.range (fun k : Fin N =>
            sigmaMin (samples k • (1 : Matrix (Fin r) (Fin r) ℂ) - Ahat)))
        let kappaΓ : ℝ :=
          sSup {s : ℝ | ∃ z : ℂ, z ∈ circle ∧
            s = operatorNorm2 ((z • (1 : Matrix (Fin r) (Fin r) ℂ)) - Ahat)⁻¹}
        (∀ z : ℂ, z ∈ circle →
            Matrix.det (z • (1 : Matrix (Fin r) (Fin r) ℂ) - Ahat) ≠ 0) →
          sStar > 2 * RΓ * Real.sin (Real.pi / (2 * (N : ℝ))) →
            kappaΓ ≤
              (sStar - 2 * RΓ * Real.sin (Real.pi / (2 * (N : ℝ))))⁻¹

end MathlibPlus.Open.Analysis
