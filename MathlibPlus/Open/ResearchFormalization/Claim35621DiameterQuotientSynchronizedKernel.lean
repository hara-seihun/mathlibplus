import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.Claim35621DiameterQuotientSynchronizedKernel

noncomputable section

private def pathEntry (i j : ℕ) : ℝ :=
  if j = i + 1 then 1 else if j = i then -1 else 0

private def pathGridMatrix (p q : ℕ) :
    Matrix (Fin (p - 1) ⊕ Fin (q - 1)) (Fin p ⊕ Fin q) ℝ :=
  fun r c =>
    match r, c with
    | Sum.inl i, Sum.inl j => pathEntry i.1 j.1
    | Sum.inl _, Sum.inr _ => 0
    | Sum.inr _, Sum.inl _ => 0
    | Sum.inr i, Sum.inr j => pathEntry i.1 j.1

private def gridCoordinate {p q : ℕ}
    (v : (Fin p → ℝ) × (Fin q → ℝ)) : Fin p ⊕ Fin q → ℝ :=
  Sum.elim v.1 v.2

private def matrixKernel (p q : ℕ)
    (v : (Fin p → ℝ) × (Fin q → ℝ)) : Prop :=
  ∀ r : Fin (p - 1) ⊕ Fin (q - 1),
    ∑ c : Fin p ⊕ Fin q,
      pathGridMatrix p q r c * gridCoordinate v c = 0

private def synchronizedKernel (p q : ℕ)
    (v : (Fin p → ℝ) × (Fin q → ℝ)) : Prop :=
  ∃ α β : ℝ,
    (∀ i : Fin p, v.1 i = α) ∧
      (∀ j : Fin q, v.2 j = β)

private def vectorDot (x y : ℝ × ℝ) : ℝ :=
  x.1 * y.1 + x.2 * y.2

private def quarterTurn (x : ℝ × ℝ) : ℝ × ℝ :=
  (-x.2, x.1)

private def gridDiagonal (p q : ℕ) : ℝ × ℝ :=
  ((p : ℝ), (q : ℝ))

private def angularVelocity {p q : ℕ}
    (a : Fin p → ℝ) (b : Fin q → ℝ) : ℝ × ℝ :=
  (∑ i : Fin p, a i) • quarterTurn (1, 0) +
    (∑ j : Fin q, b j) • quarterTurn (0, 1)

private def squaredDistanceDerivative {p q : ℕ}
    (a : Fin p → ℝ) (b : Fin q → ℝ) : ℝ :=
  2 * vectorDot (gridDiagonal p q) (angularVelocity a b)

private def plusCornerDerivative {p q : ℕ}
    (a : Fin p → ℝ) (b : Fin q → ℝ) : ℝ :=
  squaredDistanceDerivative a b

private def minusCornerDerivative {p q : ℕ}
    (a : Fin p → ℝ) (b : Fin q → ℝ) : ℝ :=
  -squaredDistanceDerivative a b

private def plusRow (p q : ℕ) : (ℝ × ℝ) → ℝ :=
  fun αβ => 2 * (p : ℝ) * (q : ℝ) * (αβ.1 - αβ.2)

private def minusRow (p q : ℕ) : (ℝ × ℝ) → ℝ :=
  fun αβ => -plusRow p q αβ

private def hexClosure
    (a a' b b' c c' : ℝ) : ℝ × ℝ :=
  (a - a') • (1, 0) +
    (b - b') • (0, 1) +
    (c - c') • (-(Real.sqrt 2)⁻¹, (Real.sqrt 2)⁻¹)

private def hexagonSynchronization : Prop :=
  ∀ a a' b b' c c' : ℝ,
    hexClosure a a' b b' c c' = (0, 0) →
      c = c' → a = a' ∧ b = b'

private def diagonalTrackSubmodule : Submodule ℝ (ℝ × ℝ) :=
  Submodule.span ℝ ({(1, 1)} : Set (ℝ × ℝ))

/-- Claim 35621: the actual path-incidence closure matrix of the orthogonal
p-by-q train-track variables has rank p+q-2 and exactly the synchronized
constant-track kernel; the actual squared-distance derivative carrier then
restricts to opposite nonzero corner rows on the one-dimensional quotient. -/
def claim35621 : Prop :=
  ∀ p q : ℕ, 2 ≤ p → 2 ≤ q →
    hexagonSynchronization ∧
    Matrix.rank (pathGridMatrix p q) = p + q - 2 ∧
    (∀ v : (Fin p → ℝ) × (Fin q → ℝ),
      matrixKernel p q v ↔ synchronizedKernel p q v) ∧
    max (p - 1) (q - 1) ≤ p + q ∧
    (∀ v : (Fin p → ℝ) × (Fin q → ℝ),
      matrixKernel p q v →
        ∃ α β : ℝ,
          (∀ i : Fin p, v.1 i = α) ∧
          (∀ j : Fin q, v.2 j = β) ∧
          plusCornerDerivative v.1 v.2 =
            2 * ((q : ℝ) * (p * α) - (p : ℝ) * (q * β)) ∧
          minusCornerDerivative v.1 v.2 =
            -2 * ((q : ℝ) * (p * α) - (p : ℝ) * (q * β))) ∧
    (∀ a : Fin p → ℝ, ∀ b : Fin q → ℝ,
      plusCornerDerivative a b =
        2 * ((q : ℝ) * (∑ i : Fin p, a i) -
          (p : ℝ) * (∑ j : Fin q, b j)) ∧
      minusCornerDerivative a b =
        -2 * ((q : ℝ) * (∑ i : Fin p, a i) -
          (p : ℝ) * (∑ j : Fin q, b j))) ∧
    (Module.finrank ℝ
      ((ℝ × ℝ) ⧸ diagonalTrackSubmodule) = 1) ∧
    (plusRow p q = fun αβ => -minusRow p q αβ) ∧
    (∀ α : ℝ, plusRow p q (α, α) = 0) ∧
    plusRow p q (1, 0) ≠ 0 ∧
    0 < (1 / 2 : ℝ) ∧
    (1 / 2 : ℝ) + 1 / 2 = 1 ∧
    (1 / 2 : ℝ) * plusRow p q (1, 0) +
        (1 / 2 : ℝ) * minusRow p q (1, 0) = 0

end

end MathlibPlus.Open.ResearchFormalization.Claim35621DiameterQuotientSynchronizedKernel
