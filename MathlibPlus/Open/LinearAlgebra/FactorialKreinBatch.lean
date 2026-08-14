import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.LinearAlgebra.FactorialKreinBatch

private noncomputable def factorialKernel (N : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  fun i j => 1 / (Nat.factorial (i.val + j.val) : ℝ)

private noncomputable def factorialPivot (j : ℕ) : ℝ :=
  if j = 0 then 1 else
    Matrix.det (factorialKernel (j + 1)) / Matrix.det (factorialKernel j)

private noncomputable def signatureDiagonal (N pos neg zero : ℕ) :
    Matrix (Fin N) (Fin N) ℝ :=
  fun i j =>
    if i = j then
      if i.val < pos then 1 else if i.val < pos + neg then -1 else 0
    else 0

private noncomputable def hasInertia (A : Matrix (Fin N) (Fin N) ℝ)
    (pos neg zero : ℕ) : Prop :=
  ∃ B : Matrix (Fin N) (Fin N) ℝ,
    B.det ≠ 0 ∧ B.transpose * A * B = signatureDiagonal N pos neg zero

private noncomputable def scaleMatrix (N : ℕ) (x : ℝ) :
    Matrix (Fin N) (Fin N) ℝ :=
  Matrix.diagonal (fun i => x ^ i.val)

private noncomputable def jumpAtom (N : ℕ) (x : ℝ) :
    Matrix (Fin N) (Fin N) ℝ :=
  fun i j => x ^ (i.val + j.val + 1) / (Nat.factorial (i.val + j.val) : ℝ)

/-- Claim 17561: determinant products and alternating pivot signs. -/
def claim17561 : Prop :=
  ∀ N : ℕ,
    Matrix.det (factorialKernel N) ≠ 0 ∧
    Matrix.det (factorialKernel N) = ∏ j : Fin N, factorialPivot j.val ∧
    (0 < Matrix.det (factorialKernel N) ↔
      0 < ∏ j : Fin N, (-1 : ℝ) ^ j.val) ∧
    (Matrix.det (factorialKernel N) < 0 ↔
      ∏ j : Fin N, (-1 : ℝ) ^ j.val < 0)

/-- Claim 17562: the exact finite inertia of the factorial kernel. -/
def claim17562 : Prop :=
  ∀ N : ℕ,
    hasInertia (factorialKernel N) ((N + 1) / 2) (N / 2) 0

/-- Claim 17563: no-pivot symmetric elimination has the alternating pivot word. -/
def claim17563 : Prop :=
  ∀ j : ℕ, factorialPivot j ≠ 0 ∧
    ((0 < factorialPivot j) ↔ Even j) ∧
    ((factorialPivot j < 0) ↔ Odd j)

/-- Claim 17564: every positive jump atom is a diagonal congruence of F. -/
def claim17564 : Prop :=
  ∀ (N : ℕ) (x : ℝ), 0 < x →
    jumpAtom N x = x • (scaleMatrix N x * factorialKernel N * scaleMatrix N x)

/-- Claim 17565: all positive jump fibers have the same finite grading. -/
def claim17565 : Prop :=
  ∀ (N : ℕ) (x : ℝ), 0 < x →
    (scaleMatrix N x).det ≠ 0 ∧
    jumpAtom N x = x • (scaleMatrix N x * factorialKernel N * scaleMatrix N x) ∧
    hasInertia (jumpAtom N x) ((N + 1) / 2) (N / 2) 0

/-- Claim 17567: the negative index of local atoms is unbounded. -/
def claim17567 : Prop :=
  ∀ (x : ℝ), 0 < x →
    (∀ N : ℕ, hasInertia (jumpAtom N x) ((N + 1) / 2) (N / 2) 0) ∧
    (∀ q : ℕ, ∃ N : ℕ, q ≤ N / 2)

end MathlibPlus.Open.LinearAlgebra.FactorialKreinBatch
