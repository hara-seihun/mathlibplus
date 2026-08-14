import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.NewResearch2.Q0002.Secant

noncomputable section

private def centralCharlier : ℕ → Polynomial ℚ
  | 0 => 1
  | n + 1 =>
      Polynomial.X * Polynomial.derivative (centralCharlier n) +
        (Polynomial.C (5 / 4) - Polynomial.X) * centralCharlier n

private def g (j : ℕ) : Polynomial ℚ := Polynomial.derivative (centralCharlier (2 * j))
private def evalMV (p : Polynomial ℚ) (z : MvPolynomial (Fin 2) ℚ) : MvPolynomial (Fin 2) ℚ :=
  p.eval₂ MvPolynomial.C z
private def exp2 (a b : ℕ) : Fin 2 →₀ ℕ :=
  Finsupp.single (0 : Fin 2) a + Finsupp.single (1 : Fin 2) b

private def secant13Formula : MvPolynomial (Fin 2) ℚ :=
  let X := MvPolynomial.X (0 : Fin 2)
  let Y := MvPolynomial.X (1 : Fin 2)
  let c : ℚ → MvPolynomial (Fin 2) ℚ := MvPolynomial.C
  c 12 * X ^ 4 * Y + c 75 * X ^ 4 + c 12 * X ^ 3 * Y ^ 2 +
    c 42 * X ^ 3 * Y - c ((825 : ℚ) / 4) * X ^ 3 + c 12 * X ^ 2 * Y ^ 3 +
    c 114 * X ^ 2 * Y ^ 2 + c ((133 : ℚ) / 4) * X ^ 2 * Y -
    c ((10525 : ℚ) / 8) * X ^ 2 + c 12 * X * Y ^ 4 + c 186 * X * Y ^ 3 +
    c ((2869 : ℚ) / 4) * X * Y ^ 2 - c ((1817 : ℚ) / 4) * X * Y -
    c ((120225 : ℚ) / 32) * X + c 3 * Y ^ 4 + c ((183 : ℚ) / 4) * Y ^ 3 +
    c ((1379 : ℚ) / 8) * Y ^ 2 - c ((3681 : ℚ) / 32) * Y - c ((34019 : ℚ) / 64)

/-- The first-gap adjacent secant has exactly the six listed negative
coefficients. -/
def claim15721 : Prop :=
  let X := MvPolynomial.X (0 : Fin 2)
  let Y := MvPolynomial.X (1 : Fin 2)
  let x : MvPolynomial (Fin 2) ℚ := MvPolynomial.C 2 + X
  let y : MvPolynomial (Fin 2) ℚ := MvPolynomial.C 8 + Y
  let gap := MvPolynomial.C 6 + Y - X
  let numerator := evalMV (g 1) x * evalMV (g 3) y -
    evalMV (g 3) x * evalMV (g 1) y
  let Q := secant13Formula
  Q * gap = numerator ∧
    Q.coeff (exp2 3 0) = (-825 : ℚ) / 4 ∧
    Q.coeff (exp2 2 0) = (-10525 : ℚ) / 8 ∧
    Q.coeff (exp2 1 1) = (-1817 : ℚ) / 4 ∧
    Q.coeff (exp2 1 0) = (-120225 : ℚ) / 32 ∧
    Q.coeff (exp2 0 1) = (-3681 : ℚ) / 32 ∧
    Q.coeff (exp2 0 0) = (-34019 : ℚ) / 64 ∧
    (∀ m, Q.coeff m < 0 →
      m = exp2 3 0 ∨ m = exp2 2 0 ∨ m = exp2 1 1 ∨
        m = exp2 1 0 ∨ m = exp2 0 1 ∨ m = exp2 0 0)

private def secant12Formula : MvPolynomial (Fin 2) ℚ :=
  let X := MvPolynomial.X (0 : Fin 2)
  let Y := MvPolynomial.X (1 : Fin 2)
  let c : ℚ → MvPolynomial (Fin 2) ℚ := MvPolynomial.C
  c 8 * X ^ 2 * Y + c 50 * X ^ 2 + c 8 * X * Y ^ 2 + c 80 * X * Y +
    c ((375 : ℚ) / 2) * X + c 2 * Y ^ 2 + c ((39 : ℚ) / 2) * Y + c ((119 : ℚ) / 4)

/-- Signed cross-gap assembly restores positivity for the adjacent pair. -/
def claim15722 : Prop :=
  let X := MvPolynomial.X (0 : Fin 2)
  let Y := MvPolynomial.X (1 : Fin 2)
  let x : MvPolynomial (Fin 2) ℚ := MvPolynomial.C 2 + X
  let y : MvPolynomial (Fin 2) ℚ := MvPolynomial.C 8 + Y
  let gap := MvPolynomial.C 6 + Y - X
  let numerator := evalMV (g 1) x * evalMV (g 2) y -
    evalMV (g 2) x * evalMV (g 1) y
  let Q := secant12Formula
  Q * gap = numerator ∧ ∀ m ∈ Q.support, 0 < Q.coeff m

end
end MathlibPlus.Open.NewResearch2.Q0002.Secant
