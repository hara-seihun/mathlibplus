import MathlibPlus.Open.Analysis.AdmittedBatch01a0014d

namespace MathlibPlus.Open.Analysis.PinnedFiniteWitnesses15140

open scoped Matrix

/-- The finite weak-pole and Jordan perturbation witnesses with the numerical
parameters reported in Claim 15140.  The weak witness keeps the common finite
observation in both radius-`ε` data balls, while the matrix witness keeps the
operator-norm distance and the two resulting eigenvalues explicit. -/
def pinnedFiniteWitnesses_claim15140 : Prop :=
  let M : ℕ := 12
  let lam : ℝ := 11 / 10
  let ε : ℝ := 1 / (10 : ℝ) ^ 8
  let a : ℝ := ε / lam ^ M
  let zeroSignal : ℕ → ℝ := fun _ => 0
  let poleSignal : ℕ → ℝ := fun n => a * lam ^ n
  let δ : ℝ := 1 / (10 : ℝ) ^ 9
  let J : Matrix (Fin 2) (Fin 2) ℂ := !![(2 : ℂ), 1; 0, 2]
  let split : Fin 2 → ℂ := ![(0 : ℂ), (δ : ℂ)]
  let Jhat : Matrix (Fin 2) (Fin 2) ℂ :=
    J + Matrix.diagonal split
  (M = 12 ∧
    lam = 11 / 10 ∧
    ε = 1 / (10 : ℝ) ^ 8 ∧
    a = ε / lam ^ 12 ∧
    0 < ε ∧
    a ≠ 0 ∧
    (∀ n : ℕ, 0 ≤ n → n ≤ M →
      |a| * |lam| ^ n ≤ ε) ∧
    |a| * |lam| ^ M = ε ∧
    (∀ n : ℕ, 0 ≤ n → n ≤ M →
      |(0 : ℝ) - zeroSignal n| ≤ ε) ∧
    (∀ n : ℕ, 0 ≤ n → n ≤ M →
      |(0 : ℝ) - poleSignal n| ≤ ε) ∧
    poleSignal 0 ≠ zeroSignal 0) ∧
  (δ = 1 / (10 : ℝ) ^ 9 ∧
    J = !![(2 : ℂ), 1; 0, 2] ∧
    J = MathlibPlus.Open.Analysis.jordanBlock 2 (2 : ℂ) ∧
    Jhat = J + Matrix.diagonal split ∧
    Jhat - J = Matrix.diagonal split ∧
    MathlibPlus.Open.Analysis.matrixOperatorNorm (Jhat - J) = δ ∧
    MathlibPlus.Open.Analysis.isMatrixEigenvalue Jhat (2 : ℂ) ∧
    MathlibPlus.Open.Analysis.isMatrixEigenvalue Jhat ((2 : ℂ) + (δ : ℂ)) ∧
    (2 : ℂ) ≠ (2 : ℂ) + (δ : ℂ))

end MathlibPlus.Open.Analysis.PinnedFiniteWitnesses15140
