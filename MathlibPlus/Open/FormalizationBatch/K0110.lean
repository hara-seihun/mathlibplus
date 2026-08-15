import Mathlib

namespace MathlibPlus.Open.FormalizationBatch.K0110

noncomputable section

/-- The affine matrix pencil specified by its canonical endpoint and slope. -/
def affinePencil {n : ℕ} (b₀ : ℝ)
    (P₀ S : Matrix (Fin n) (Fin n) ℝ) : ℝ → Matrix (Fin n) (Fin n) ℝ :=
  fun b => P₀ + (b - b₀) • S

/-- The leading principal `k`-section of an `n`-by-`n` matrix. -/
def leadingSection {n k : ℕ} (hk : k ≤ n)
    (P : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin k) (Fin k) ℝ :=
  P.submatrix (Fin.castLE hk) (Fin.castLE hk)

/-- The canonical inverse square root obtained from the Hermitian spectral basis. -/
noncomputable def canonicalInverseSqrt {n : ℕ}
    (P : Matrix (Fin n) (Fin n) ℝ) (hP : P.PosDef) : Matrix (Fin n) (Fin n) ℝ :=
  let hermitian := hP.isHermitian
  let eigenvalues := hermitian.eigenvalues
  let eigenbasis := hermitian.eigenvectorBasis
  let inverseSquareRoots : Fin n → EuclideanSpace ℝ (Fin n) :=
    fun i => (Real.sqrt (eigenvalues i))⁻¹ • eigenbasis i
  let diagonalAction : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) :=
    eigenbasis.toBasis.constr ℝ inverseSquareRoots
  let standard := EuclideanSpace.basisFun (Fin n) ℝ
  (Matrix.toLin standard.toBasis standard.toBasis).symm diagonalAction

/-- The operator 2-norm of a real square matrix. -/
noncomputable def operatorTwoNorm {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  let standard := EuclideanSpace.basisFun (Fin n) ℝ
  ‖((Matrix.toLin standard.toBasis standard.toBasis) A).toContinuousLinearMap‖

/-- Uniform positivity along the homotopy. -/
def uniformPositivityAlongHomotopy8663 : Prop :=
  ∀ (n : ℕ) (b b₀ Δ η : ℝ)
    (N₀ M₀ S_N S_M : Matrix (Fin n) (Fin n) ℝ)
    (hN₀ : N₀.PosDef) (hM₀ : M₀.PosDef)
    (hNsymm : ∀ t : ℝ, (affinePencil b₀ N₀ S_N t).IsSymm)
    (hMsymm : ∀ t : ℝ, (affinePencil b₀ M₀ S_M t).IsSymm),
    let N := affinePencil b₀ N₀ S_N
    let M := affinePencil b₀ M₀ S_M
    let A_N :=
      canonicalInverseSqrt N₀ hN₀ * S_N * canonicalInverseSqrt N₀ hN₀
    let A_M :=
      canonicalInverseSqrt M₀ hM₀ * S_M * canonicalInverseSqrt M₀ hM₀
    let L := max (operatorTwoNorm A_N) (operatorTwoNorm A_M)
    |b - b₀| ≤ Δ →
    η = Δ * L →
    η < 1 →
    ∀ (k : ℕ) (hk₁ : 1 ≤ k) (hk : k ≤ n),
      (leadingSection hk (N b)).PosDef ∧
        (leadingSection hk (M b)).PosDef

end

end MathlibPlus.Open.FormalizationBatch.K0110
