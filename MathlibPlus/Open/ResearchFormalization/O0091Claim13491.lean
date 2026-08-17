import MathlibPlus.Open.LinearAlgebra.BatchO0091

open scoped BigOperators Matrix

namespace MathlibPlus.Open.ResearchFormalization.O0091Claim13491

noncomputable section

open MathlibPlus.Open.LinearAlgebra

abbrev ChoiIndex := JointIndex × JointIndex
abbrev ChoiMatrix := Matrix ChoiIndex ChoiIndex ℂ

/-- The Choi matrix of the concrete four-dimensional heat channel. -/
noncomputable def choiMatrix (lam : ℝ) : ChoiMatrix :=
  fun i j => heatChannel lam (matrixUnit i.1 j.1) i.2 j.2

/-- The normalized Choi state, with the input dimension-four normalization. -/
noncomputable def normalizedChoi (lam : ℝ) : ChoiMatrix :=
  (1 / 4 : ℂ) • choiMatrix lam

/-- Partial transpose on the reference factor of the Choi carrier. -/
noncomputable def referencePartialTranspose (M : ChoiMatrix) : ChoiMatrix :=
  fun i j => M (j.1, i.2) (i.1, j.2)

noncomputable def normalizedChoiPartialTranspose (lam : ℝ) : ChoiMatrix :=
  referencePartialTranspose (normalizedChoi lam)

/-- The trace norm, expressed by the finite singular-value sum. -/
noncomputable def choiTraceNorm (lam : ℝ) : ℝ :=
  ∑ k : Fin 16,
    (Matrix.toEuclideanLin (normalizedChoiPartialTranspose lam)).singularValues k

noncomputable def choiNegativity (lam : ℝ) : ℝ :=
  (choiTraceNorm lam - 1) / 2

noncomputable def choiLogarithmicNegativity (lam : ℝ) : ℝ :=
  binaryLog (choiTraceNorm lam)

/-- Exact Choi negativity and logarithmic-negativity formulas. -/
def claim13491 : Prop :=
  ∀ lam : ℝ, |lam| ≤ 1 →
    choiNegativity lam = negativity lam ∧
      choiLogarithmicNegativity lam = logarithmicNegativity lam ∧
      negativity lam = |lam| / 2 ∧
      logarithmicNegativity lam = binaryLog (1 + |lam|)

end

end MathlibPlus.Open.ResearchFormalization.O0091Claim13491
