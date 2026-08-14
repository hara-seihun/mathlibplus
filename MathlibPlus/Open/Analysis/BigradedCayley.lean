import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.Analysis.BigradedCayley

/-- Claim 4897: factorial-jet and affine-sector bilinear forms remain separate
factors: an alternating-sign symmetric form and a nondegenerate skew form on
distinct coordinate types. -/
def claim4897 (N m : ℕ)
    (D : Matrix (Fin N) (Fin N) ℝ)
    (J : Matrix (Fin m) (Fin m) ℝ) : Prop :=
  (2 ≤ N) ∧
    (∀ i j : Fin N, D i j = D j i) ∧
    (∀ i j : Fin N, i ≠ j → D i j = 0) ∧
    (∀ i : Fin N, 0 < ((-1 : ℝ) ^ i.1) * D i i) ∧
    (∀ i j : Fin m, J i j = -J j i) ∧
    Matrix.det J ≠ 0

/-- Claim 4901: the Hamiltonian Cayley transform has no quadratic term and its
first possible remainder after the linear term is cubic.  Inverse equations
are used rather than an untyped inverse operation. -/
def claim4901 (n : ℕ) : Prop :=
  ∀ (J X : Matrix (Fin n) (Fin n) ℝ)
    (M : Matrix (Fin n) (Fin n) ℝ → Matrix (Fin n) (Fin n) ℝ),
    (∀ i j : Fin n, J i j = -J j i) →
    Matrix.det J ≠ 0 →
    (∀ i j : Fin n,
      (∑ k : Fin n, X k i * J k j) +
        ∑ k : Fin n, J i k * X k j = 0) →
    (∀ W B : Matrix (Fin n) (Fin n) ℝ,
      (∀ i k, ∑ j : Fin n,
        (W i j + if i = j then 1 else 0) * B j k = if i = k then 1 else 0) ∧
      (∀ i k, ∑ j : Fin n,
        B i j * (W j k + if j = k then 1 else 0) = if i = k then 1 else 0) →
        (∀ i j, M W i j =
          ∑ k : Fin n, J i k *
            ∑ l : Fin n, (W k l - if k = l then 1 else 0) * B l j)) →
      let E : ℝ → Matrix (Fin n) (Fin n) ℝ := fun t i j ↦
        ∑' k : ℕ, ((t • X) ^ k) i j / (Nat.factorial k : ℝ)
      ∃ C δ : ℝ, 0 ≤ C ∧ 0 < δ ∧
        ∀ t : ℝ, |t| < δ →
          ∀ i j : Fin n,
            |M (E t) i j -
                (t / 2) * ∑ k : Fin n, J i k * X k j| ≤ C * |t| ^ 3

/-- Claim 4902: the finite crossing form is the tensor product of the
factorial-jet form with the affine-sector Cayley form. -/
def claim4902 (N n : ℕ) : Prop :=
  ∀ (D : Matrix (Fin N) (Fin N) ℝ)
    (M : Matrix (Fin n) (Fin n) ℝ → Matrix (Fin n) (Fin n) ℝ)
    (W : Matrix (Fin n) (Fin n) ℝ)
    (MN : Matrix (Fin N × Fin n) (Fin N × Fin n) ℝ),
    ∀ i j : Fin N, ∀ a b : Fin n,
      MN (i, a) (j, b) = D i j * (M W) a b

end MathlibPlus.Open.Analysis.BigradedCayley
