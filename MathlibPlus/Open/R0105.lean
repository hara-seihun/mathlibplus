import Mathlib

noncomputable section
open scoped BigOperators

namespace MathlibPlus.Open.R0105

private def swap : Matrix (Fin 2) (Fin 2) ℝ := fun i j =>
  if i = 0 ∧ j = 1 then 1 else
  if i = 1 ∧ j = 0 then 1 else 0

private def qOperator (ξ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := fun i j =>
  if i = j then Real.cosh (2 * ξ) else Real.sinh (2 * ξ)

private def qHalf (ξ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := fun i j =>
  if i = j then Real.cosh ξ else Real.sinh ξ

/-- The explicit inverse of Qξ+I, used to expose the Cayley formula without
any undeclared inverse operator. -/
private def qPlusInverse (ξ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := fun i j =>
  if i = j then
    (Real.cosh (2 * ξ) + 1) /
      (4 * (Real.cosh ξ) ^ 2)
  else
    -(Real.sinh (2 * ξ)) /
      (4 * (Real.cosh ξ) ^ 2)

private def cayleyA (ξ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  (qOperator ξ - 1) * qPlusInverse ξ

private def sech (ξ : ℝ) : ℝ := 1 / Real.cosh ξ

private def cayleyB (ξ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  (2 : ℝ) • (qHalf ξ * qPlusInverse ξ)

/-- Exact Cayley A formula. -/
def claim_17983 : Prop :=
  ∀ ξ : ℝ, cayleyA ξ = Real.tanh ξ • swap

/-- Exact Cayley B formula. -/
def claim_17984 : Prop :=
  ∀ ξ : ℝ, cayleyB ξ = sech ξ • (1 : Matrix (Fin 2) (Fin 2) ℝ)

private def julia (ξ : ℝ) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℝ :=
  fun i j => match i, j with
  | Sum.inl i, Sum.inl j => cayleyA ξ i j
  | Sum.inl i, Sum.inr j => cayleyB ξ i j
  | Sum.inr i, Sum.inl j => cayleyB ξ i j
  | Sum.inr i, Sum.inr j => -(cayleyA ξ i j)

/-- The Julia block is a real self-adjoint unitary. -/
def claim_17986 : Prop :=
  ∀ ξ : ℝ,
    julia ξ = Matrix.transpose (julia ξ) ∧
    Matrix.transpose (julia ξ) * julia ξ =
      (1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℝ) ∧
    julia ξ * julia ξ =
      (1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℝ)

private def gaussian (ξ : ℝ) (z : Fin 2 → ℝ) : ℝ :=
  Real.exp
    (-Real.pi * ∑ i : Fin 2, z i * ((qOperator ξ).mulVec z i))

private def coordinateDirection (i : Fin 2) : Fin 2 → ℝ := fun j =>
  if i = j then 1 else 0

/-- Directional form of the matrix-valued first-Hermite score formula. -/
def claim_17991 : Prop :=
  ∀ (ξ : ℝ) (z : Fin 2 → ℝ) (i : Fin 2),
    HasDerivAt
      (fun t : ℝ => gaussian ξ (z + t • coordinateDirection i))
      (-2 * Real.pi * ((qOperator ξ).mulVec z i) * gaussian ξ z) 0

end MathlibPlus.Open.R0105
