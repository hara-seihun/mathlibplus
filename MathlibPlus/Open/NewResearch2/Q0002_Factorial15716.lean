import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.NewResearch2.Q0002.Factorial15716

noncomputable section

private def factorialBasisPolynomial (a : Fin 3 → ℝ) (k : Fin 4) : Polynomial ℝ :=
  match k.1 with
  | 0 => 1
  | 1 => Polynomial.X - Polynomial.C (a 0)
  | 2 => (Polynomial.X - Polynomial.C (a 0)) *
      (Polynomial.X - Polynomial.C (a 1))
  | _ => (Polynomial.X - Polynomial.C (a 0)) *
      (Polynomial.X - Polynomial.C (a 1)) *
      (Polynomial.X - Polynomial.C (a 2))

private def g1Polynomial : Polynomial ℝ :=
  2 * Polynomial.X - Polynomial.C (7 / 2 : ℝ)

private def g2Polynomial : Polynomial ℝ :=
  4 * Polynomial.X ^ 3 - 33 * Polynomial.X ^ 2 +
    Polynomial.C (251 / 4 : ℝ) * Polynomial.X -
      Polynomial.C (371 / 16 : ℝ)

private def g1Coefficient (a : Fin 3 → ℝ) (k : Fin 4) : ℝ :=
  match k.1 with
  | 0 => 2 * a 0 - 7 / 2
  | 1 => 2
  | _ => 0

private def g2Coefficient (a : Fin 3 → ℝ) (k : Fin 4) : ℝ :=
  let c₂ := 4 * (a 0 + a 1 + a 2) - 33
  let c₁ := 251 / 4 + c₂ * (a 0 + a 1) -
    4 * (a 0 * a 1 + a 0 * a 2 + a 1 * a 2)
  match k.1 with
  | 0 => 4 * a 0 ^ 3 - 33 * a 0 ^ 2 +
      (251 / 4 : ℝ) * a 0 - 371 / 16
  | 1 => c₁
  | 2 => c₂
  | _ => 4

private def coefficientMinor (a : Fin 3 → ℝ) (i j : Fin 4) : ℝ :=
  g1Coefficient a i * g2Coefficient a j -
    g1Coefficient a j * g2Coefficient a i

private def g1Expansion (a : Fin 3 → ℝ) : Polynomial ℝ :=
  ∑ k : Fin 4,
    Polynomial.C (g1Coefficient a k) * factorialBasisPolynomial a k

private def g2Expansion (a : Fin 3 → ℝ) : Polynomial ℝ :=
  ∑ k : Fin 4,
    Polynomial.C (g2Coefficient a k) * factorialBasisPolynomial a k

private def factorialEvaluation (a : Fin 3 → ℝ) (k : Fin 4)
    (z : MvPolynomial (Fin 2) ℝ) : MvPolynomial (Fin 2) ℝ :=
  let c : ℝ → MvPolynomial (Fin 2) ℝ := MvPolynomial.C
  match k.1 with
  | 0 => 1
  | 1 => z - c (a 0)
  | 2 => (z - c (a 0)) * (z - c (a 1))
  | _ => (z - c (a 0)) * (z - c (a 1)) * (z - c (a 2))

private def shiftedFactorialSchurMinor (a : Fin 3 → ℝ) (i j : Fin 4) :
    MvPolynomial (Fin 2) ℝ :=
  let c : ℝ → MvPolynomial (Fin 2) ℝ := MvPolynomial.C
  let x₁ := c 2 + MvPolynomial.X (0 : Fin 2)
  let x₂ := c 8 + MvPolynomial.X (1 : Fin 2)
  factorialEvaluation a i x₁ * factorialEvaluation a j x₂ -
    factorialEvaluation a j x₁ * factorialEvaluation a i x₂

private def coefficientwiseNonnegative
    (P : MvPolynomial (Fin 2) ℝ) : Prop :=
  ∀ m : Fin 2 →₀ ℕ, 0 ≤ P.coeff m

private def y₂SquaredCoefficient (a : Fin 3 → ℝ) : ℝ :=
  (shiftedFactorialSchurMinor a 1 2).coeff
    (Finsupp.single (1 : Fin 2) 2)

private def U (x : ℝ) : ℝ :=
  (x ^ 2 - 20 * x + 96) / (8 - x)

private def y₁Coefficient (a : Fin 3 → ℝ) : ℝ :=
  a 0 ^ 2 - 20 * a 0 + 96 - (8 - a 0) * (a 1 + a 2)

private def orderedNodes (a : Fin 3 → ℝ) : Prop :=
  a 0 ≤ a 1 ∧ a 1 ≤ a 2

private def factorialBasisConditions (a : Fin 3 → ℝ) : Prop :=
  orderedNodes a ∧
    g1Expansion a = g1Polynomial ∧
    g2Expansion a = g2Polynomial ∧
    (∀ i j : Fin 4, i.1 < j.1 →
      0 ≤ coefficientMinor a i j) ∧
    (∀ i j : Fin 4, i.1 < j.1 →
      coefficientwiseNonnegative (shiftedFactorialSchurMinor a i j)) ∧
    coefficientMinor a 1 3 = 8 ∧
    0 ≤ y₂SquaredCoefficient a ∧
    y₂SquaredCoefficient a = 2 - a 0 ∧
    0 ≤ y₁Coefficient a

private def N (x y : ℝ) : ℝ :=
  32 * x ^ 2 * y - 56 * x ^ 2 + 32 * x * y ^ 2 - 320 * x * y +
    462 * x - 56 * y ^ 2 + 462 * y - 693

/-- Claim 15716: the packet's ordered factorial basis, its two explicit
columns, oriented coefficient minors, both shifted coefficient signs, and the
full convex-endpoint arithmetic chain are retained together. -/
def claim15716 : Prop :=
  (∀ a : Fin 3 → ℝ, factorialBasisConditions a →
    coefficientMinor a 1 3 = 8 ∧
      coefficientMinor a 0 3 = 8 * a 0 - 14 ∧
      7 / 4 ≤ a 0 ∧
      0 ≤ y₂SquaredCoefficient a ∧
      y₂SquaredCoefficient a = 2 - a 0 ∧
      a 0 ≤ 2 ∧
      0 ≤ y₁Coefficient a ∧
      a 1 + a 2 ≤ U (a 0) ∧
      a 1 ≤ U (a 0) / 2 ∧
      a 0 ≤ a 1 ∧
      coefficientMinor a 0 1 = N (a 0) (a 1) / 4 ∧
      N (a 0) (a 1) < 0 ∧
      coefficientMinor a 0 1 < 0) ∧
  (∀ x : ℝ, 7 / 4 ≤ x → x ≤ 2 →
    ConvexOn ℝ Set.univ (fun y => N x y)) ∧
  (∀ x : ℝ, 7 / 4 ≤ x → x ≤ 2 →
    ∀ y : ℝ, x ≤ y → y ≤ U x / 2 →
      N x y ≤ max (N x x) (N x (U x / 2))) ∧
  (∀ x : ℝ, 7 / 4 ≤ x → x ≤ 2 →
    N x x = 64 * x ^ 3 - 432 * x ^ 2 + 924 * x - 693) ∧
  (∀ x : ℝ, 7 / 4 ≤ x → x ≤ 2 →
    N x (U x / 2) = -8 * x ^ 3 + 90 * x ^ 2 - 201 * x + 63) ∧
  (∀ x : ℝ, 7 / 4 ≤ x → x ≤ 2 → N x x < 0) ∧
  (∀ x : ℝ, 7 / 4 ≤ x → x ≤ 2 → N x (U x / 2) < 0) ∧
  (∀ t : ℝ, 0 ≤ t → t ≤ 1 / 4 →
    N (2 - t) (2 - t) =
      -61 + 36 * t - 48 * t ^ 2 - 64 * t ^ 3 ∧
    N (2 - t) (U (2 - t) / 2) =
      -43 - 63 * t + 42 * t ^ 2 + 8 * t ^ 3 ∧
    -61 + 36 * t - 48 * t ^ 2 - 64 * t ^ 3 < 0 ∧
    -43 - 63 * t + 42 * t ^ 2 + 8 * t ^ 3 < 0)

end
end MathlibPlus.Open.NewResearch2.Q0002.Factorial15716
