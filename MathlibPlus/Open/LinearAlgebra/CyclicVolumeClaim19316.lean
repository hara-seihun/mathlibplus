import Mathlib

namespace MathlibPlus.Open.LinearAlgebra.CyclicVolumes

noncomputable section

private def cyclicVolumeWithTheta (d theta : ℕ → ℝ) (i j k : ℕ) : ℝ :=
  Matrix.det ![
    ![d i, d i * theta i, d i * (i : ℝ) / 2],
    ![d j, d j * theta j, d j * (j : ℝ) / 2],
    ![d k, d k * theta k, d k * (k : ℝ) / 2]
  ]

private def decoratedZero (alpha t₀ : ℝ) : Fin 4 → ℝ :=
  ![0, 1, alpha * t₀, 0]

private def decoratedPoint (d theta : ℕ → ℝ) (n : ℕ) : Fin 4 → ℝ :=
  ![-d n * (n : ℝ) / 2, 0, -d n, -d n * theta n]

/-- Claim 19316: the determinant of the decorated flag vectors is exactly the
cyclic three-volume for every ordered positive triple. -/
def claim_19316 : Prop :=
  ∀ (alpha t₀ : ℝ) (d theta : ℕ → ℝ) (i j k : ℕ),
    1 ≤ i → i < j → j < k →
      Matrix.det ![
        decoratedZero alpha t₀,
        decoratedPoint d theta i,
        decoratedPoint d theta j,
        decoratedPoint d theta k
      ] = cyclicVolumeWithTheta d theta i j k

end

end MathlibPlus.Open.LinearAlgebra.CyclicVolumes
