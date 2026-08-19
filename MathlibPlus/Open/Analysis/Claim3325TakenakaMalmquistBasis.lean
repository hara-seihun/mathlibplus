import MathlibPlus.Open.Analysis.Claim3326

namespace MathlibPlus.Open.Analysis.Claim3325

/-- Claim 3325: the normalized Takenaka--Malmquist functions, their actual
inverse Laplace transforms, and their orthonormality are the reviewed basis
carrier on the smooth dense train. -/
def takenakaMalmquistBasis_claim3325
    (N : ℝ → ℕ) (y t : ℝ → ℕ → ℝ)
    (phi : ℝ → ℕ → ℝ → ℂ) : Prop :=
  MathlibPlus.Open.Analysis.Claim3326.takenakaMalmquistBasis N y t phi

end MathlibPlus.Open.Analysis.Claim3325
