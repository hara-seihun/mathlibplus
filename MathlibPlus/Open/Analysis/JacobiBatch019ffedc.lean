import Mathlib

open scoped BigOperators Matrix

namespace MathlibPlus.Open.Analysis.JacobiBatch

private def irreducibleJacobi
    (n : ℕ) (J : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) : Prop :=
  J.transpose = J ∧
    (∀ i j, i.val + 1 < j.val ∨ j.val + 1 < i.val → J i j = 0) ∧
    (∀ i : Fin n, 0 < J i.castSucc i.succ)

private def eZero (n : ℕ) : Fin (n + 1) → ℝ :=
  fun i => if i = 0 then 1 else 0

private def vacuumPinned
    {n : ℕ} (E : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) : Prop :=
  E.transpose = E ∧ ∀ i, E i 0 = 0

private def commutator
    {n : ℕ} (J E : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  J * E - E * J

private def frobeniusSq
    {n : ℕ} (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) : ℝ :=
  ∑ i : Fin (n + 1), ∑ j : Fin (n + 1), (M i j) ^ 2

private def isMinimumGap
    {n : ℕ} (x : Fin (n + 1) → ℝ) (δ : ℝ) : Prop :=
  (∃ i j, i ≠ j ∧ δ = |x i - x j|) ∧
    ∀ i j, i ≠ j → δ ≤ |x i - x j|

private def isMinimumWeight
    {n : ℕ} (g : Fin (n + 1) → ℝ) (ω : ℝ) : Prop :=
  (∃ i, ω = (g i) ^ 2) ∧ ∀ i, ω ≤ (g i) ^ 2

/-- Claim 7302: irreducible Jacobi first coordinate is cyclic. -/
def irreducibleJacobiFirstCoordinateCyclic : Prop :=
  ∀ (n : ℕ) (J : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ),
    irreducibleJacobi n J →
      Matrix.det (fun i j => (J ^ j.val) i 0) ≠ 0 ∧
        ∀ (V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
          (x : Fin (n + 1) → ℝ),
          V.transpose * V = 1 →
            J = V * Matrix.diagonal x * V.transpose →
              (Matrix.det (fun i j => (J ^ j.val) i 0) ≠ 0 ↔
                ∀ i, (V.transpose *ᵥ eZero n) i ≠ 0)

/-- Claim 7303: the vacuum-pinned Jacobi commutator map is bijective. -/
def vacuumPinnedJacobiCommutatorBijection : Prop :=
  ∀ (n : ℕ) (J : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ),
    irreducibleJacobi n J →
      (∀ E₁ E₂ : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ,
        vacuumPinned E₁ → vacuumPinned E₂ →
          commutator J E₁ = commutator J E₂ → E₁ = E₂) ∧
      (∀ A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ,
        A.transpose = -A →
          ∃ E : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ,
            vacuumPinned E ∧ commutator J E = A)

/-- Claim 7304: off-diagonal entries of the spectral inverse. -/
def explicitOffDiagonalSpectralInverse : Prop :=
  ∀ (n : ℕ)
    (J V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (x : Fin (n + 1) → ℝ)
    (A E : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ),
    irreducibleJacobi n J →
      V.transpose * V = 1 →
        J = V * Matrix.diagonal x * V.transpose →
          vacuumPinned E → commutator J E = A →
            ∀ i j, i ≠ j →
              (V.transpose * E * V) i j =
                (V.transpose * A * V) i j / (x i - x j)

/-- Claim 7305: the vacuum pin determines the diagonal spectral entries. -/
def diagonalSpectralEntriesFromVacuumPin : Prop :=
  ∀ (n : ℕ)
    (J V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (x : Fin (n + 1) → ℝ)
    (A E : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ),
    irreducibleJacobi n J →
      V.transpose * V = 1 →
        J = V * Matrix.diagonal x * V.transpose →
          vacuumPinned E → commutator J E = A →
            let g : Fin (n + 1) → ℝ := V.transpose *ᵥ eZero n
            let Ehat := V.transpose * E * V
            (∀ i, g i ≠ 0) ∧
              ∀ i, Ehat i i = -(g i)⁻¹ *
                ∑ j : Fin (n + 1), if j ≠ i then Ehat i j * g j else 0

/-- Claim 7306: gap/weight Frobenius conditioning bound. -/
def gapWeightFrobeniusConditioningBound : Prop :=
  ∀ (n : ℕ)
    (J V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (x : Fin (n + 1) → ℝ)
    (A E : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (δ ω : ℝ),
    irreducibleJacobi n J →
      V.transpose * V = 1 →
        J = V * Matrix.diagonal x * V.transpose →
          isMinimumGap x δ →
            isMinimumWeight (V.transpose *ᵥ eZero n) ω →
              vacuumPinned E → commutator J E = A →
                frobeniusSq E ≤
                  (1 + ω⁻¹) * (δ⁻¹) ^ 2 * frobeniusSq A

end MathlibPlus.Open.Analysis.JacobiBatch
