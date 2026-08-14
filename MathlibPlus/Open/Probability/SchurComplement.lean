import Mathlib

noncomputable section

namespace MathlibPlus.Open.Probability.SchurComplement

open scoped BigOperators

private def quadratic {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (x : Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j, x i * A i j * x j

private def symmetric {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ i j, A i j = A j i

private def covarianceBlock {m n : ℕ}
    (K : Matrix (Fin m) (Fin m) ℝ)
    (C : Matrix (Fin m) (Fin n) ℝ)
    (L : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℝ :=
  fun i j =>
    match i, j with
    | Sum.inl i, Sum.inl j => K i j
    | Sum.inl i, Sum.inr j => C i j
    | Sum.inr i, Sum.inl j => C j i
    | Sum.inr i, Sum.inr j => L i j

private def schurComplement {m n : ℕ}
    (K : Matrix (Fin m) (Fin m) ℝ)
    (C : Matrix (Fin m) (Fin n) ℝ)
    (L : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin m) (Fin m) ℝ :=
  K - C * L⁻¹ * C.transpose

private def shearLift {m n : ℕ}
    (U : Matrix (Fin m) (Fin n) ℝ)
    (V : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℝ :=
  fun i j =>
    match i, j with
    | Sum.inl i, Sum.inl j => if i = j then 1 else 0
    | Sum.inl i, Sum.inr j => U i j
    | Sum.inr i, Sum.inl _ => 0
    | Sum.inr i, Sum.inr j => V i j

/-- Invertible changes of conditioned coordinates and shears of observed
coordinates act by block-triangular congruence and preserve the Schur complement. -/
def claim_19258 : Prop :=
  ∀ (m n : ℕ)
    (K : Matrix (Fin m) (Fin m) ℝ)
    (C : Matrix (Fin m) (Fin n) ℝ)
    (L : Matrix (Fin n) (Fin n) ℝ)
    (U : Matrix (Fin m) (Fin n) ℝ)
    (V : Matrix (Fin n) (Fin n) ℝ),
    symmetric K → symmetric L → Matrix.det L ≠ 0 → Matrix.det V ≠ 0 →
      (let K' := K + U * C.transpose + C * U.transpose + U * L * U.transpose
       let C' := (C + U * L) * V.transpose
       let L' := V * L * V.transpose
       schurComplement K' C' L' = schurComplement K C L ∧
         covarianceBlock K' C' L' =
           shearLift U V * covarianceBlock K C L * (shearLift U V).transpose)

end MathlibPlus.Open.Probability.SchurComplement
