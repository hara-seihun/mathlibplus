import Mathlib

noncomputable section

namespace MathlibPlus.Open.Research.FormalizationR0216

private def positiveQuadraticForm {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ x : Fin n → ℝ, x ≠ 0 →
    0 < ∑ i : Fin n, x i * (A.mulVec x) i

private def realSpectralRadius {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  sSup {r : ℝ |
    ∃ lam : ℝ, r = |lam| ∧
      ∃ v : Fin n → ℝ, v ≠ 0 ∧ A.mulVec v = lam • v}

private def euclideanVectorNorm {n : ℕ} (v : Fin n → ℝ) : ℝ :=
  Real.sqrt (∑ i : Fin n, v i ^ 2)

private def euclideanOperatorNorm {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  sSup {r : ℝ |
    ∃ v : Fin n → ℝ,
      euclideanVectorNorm v = 1 ∧
        r = euclideanVectorNorm (A.mulVec v)}

/-- Claim 18906: under the real symmetric positive-definite hypotheses, the
spectral radius of the inverse-normalized perturbation equals the Euclidean
operator norm of the symmetric inverse-square-root normalization. -/
def intrinsicNormalizedPerturbationSize18906 : Prop :=
  ∀ (n : ℕ)
    (G Δ Gi H : Matrix (Fin n) (Fin n) ℝ),
    G = G.transpose →
    Δ = Δ.transpose →
    positiveQuadraticForm G →
    G * Gi = 1 →
    Gi * G = 1 →
    H = H.transpose →
    positiveQuadraticForm H →
    H * H = Gi →
      realSpectralRadius (Gi * Δ) =
        euclideanOperatorNorm (H * Δ * H)

end MathlibPlus.Open.Research.FormalizationR0216
