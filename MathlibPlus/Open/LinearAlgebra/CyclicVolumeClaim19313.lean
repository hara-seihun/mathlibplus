import Mathlib

namespace MathlibPlus.Open.LinearAlgebra.CyclicVolumes

noncomputable section

private def cyclicVolume (d delta : ℕ → ℝ) (i j k : ℕ) : ℝ :=
  Matrix.det ![
    ![d i, -(d i * delta i), d i * (i : ℝ) / 2],
    ![d j, -(d j * delta j), d j * (j : ℝ) / 2],
    ![d k, -(d k * delta k), d k * (k : ℝ) / 2]
  ]

/-- Claim 19313: with positive amplitudes, ordered cyclic-volume positivity is
exactly strict positivity of every displayed discrete-curvature factor. -/
def claim_19313 : Prop :=
  ∀ (d delta : ℕ → ℝ),
    (∀ n : ℕ, 0 < d n) →
      ((∀ (i j k : ℕ), i < j → j < k →
          0 < cyclicVolume d delta i j k) ↔
        (∀ (i j k : ℕ), i < j → j < k →
          0 < (((k : ℝ) - j) * delta i -
            ((k : ℝ) - i) * delta j +
            ((j : ℝ) - i) * delta k)))

end

end MathlibPlus.Open.LinearAlgebra.CyclicVolumes
