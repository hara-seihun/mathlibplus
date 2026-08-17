import MathlibPlus.Open.Probability.PosteriorVarianceGamma

namespace MathlibPlus.Open.ResearchFormalization.R3656

noncomputable section

/-- The ordinary 33-fold confluent determinant of the even-moment functions. -/
noncomputable def W33_claim47532 (y : ℝ) : ℝ :=
  Matrix.det (fun i j : Fin 33 =>
    iteratedDeriv (i : ℕ) (MathlibPlus.Open.Probability.gammaEvenMoment (j : ℕ)) y)

/-- The midpoint determinant at an integer anchor. -/
noncomputable def DAnchor_claim47533 (a : ℤ) : ℝ :=
  Matrix.det (fun i j : Fin 33 =>
    MathlibPlus.Open.Probability.gammaEvenMoment (j : ℕ)
      (Real.log ((a : ℝ) + ((i : ℕ) : ℝ) + (1 / 2 : ℝ))))

/-- Positive integer anchors place each logarithmic midpoint in its open cell. -/
def logarithmicMidpointOpenCells_claim47533 : Prop :=
  ∀ a : ℤ, 0 < a → ∀ i : Fin 33,
    Real.log ((a : ℝ) + ((i : ℕ) : ℝ)) <
        Real.log ((a : ℝ) + ((i : ℕ) : ℝ) + (1 / 2 : ℝ)) ∧
      Real.log ((a : ℝ) + ((i : ℕ) : ℝ) + (1 / 2 : ℝ)) <
        Real.log ((a : ℝ) + ((i : ℕ) : ℝ) + 1)

end

end MathlibPlus.Open.ResearchFormalization.R3656
