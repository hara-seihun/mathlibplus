import MathlibPlus.Open.GaugedCrossRatio

namespace MathlibPlus.Open.ResearchFormalization.K0135GaugedDeterminantClaim9056

open scoped BigOperators

noncomputable section

/-- The finite gauged lattice heat matrix, indexed by `Fin m`. -/
noncomputable def gaugedHeatMatrix9056 (γ : ℝ) (n m : ℕ) :
    Matrix (Fin m) (Fin m) ℝ :=
  fun r s =>
    Real.exp
      (-γ * (((r : ℕ) : ℝ) - ((s : ℕ) : ℝ)) ^ 2 / (n : ℝ))

/--
Claim 9056: Gaussian gauging factors the lattice heat matrix through
`q = exp (2γ/n)`, and its determinant is the reviewed gauged determinant
carrier.
-/
def claim9056_gaussianGaugedHeatDeterminant : Prop :=
  ∀ (n m : ℕ) (γ : ℝ), 1 ≤ n →
    let q : ℝ := Real.exp (2 * γ / (n : ℝ))
    let H : Matrix (Fin m) (Fin m) ℝ := gaugedHeatMatrix9056 γ n m
    (∀ r s : Fin m,
      H r s =
        Real.exp (-γ * ((r : ℕ) : ℝ) ^ 2 / (n : ℝ)) *
          q ^ ((r : ℕ) * (s : ℕ)) *
          Real.exp (-γ * ((s : ℕ) : ℝ) ^ 2 / (n : ℝ))) ∧
      Matrix.det H = MathlibPlus.Open.gaugedHeatDeterminant γ n m

end

end MathlibPlus.Open.ResearchFormalization.K0135GaugedDeterminantClaim9056
