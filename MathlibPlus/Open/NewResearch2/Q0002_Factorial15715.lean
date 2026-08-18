import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.NewResearch2.Q0002.Factorial15715

noncomputable section

def factorialBasisPolynomial (a : Fin 3 → ℝ) (k : Fin 4) : Polynomial ℝ :=
  match k.1 with
  | 0 => 1
  | 1 => Polynomial.X - Polynomial.C (a 0)
  | 2 => (Polynomial.X - Polynomial.C (a 0)) *
      (Polynomial.X - Polynomial.C (a 1))
  | _ => (Polynomial.X - Polynomial.C (a 0)) *
      (Polynomial.X - Polynomial.C (a 1)) *
      (Polynomial.X - Polynomial.C (a 2))

def g1Polynomial : Polynomial ℝ :=
  2 * Polynomial.X - Polynomial.C (7 / 2 : ℝ)

def g2Polynomial : Polynomial ℝ :=
  4 * Polynomial.X ^ 3 - 33 * Polynomial.X ^ 2 +
    Polynomial.C (251 / 4 : ℝ) * Polynomial.X -
      Polynomial.C (371 / 16 : ℝ)

def g1Coefficient (a : Fin 3 → ℝ) (k : Fin 4) : ℝ :=
  match k.1 with
  | 0 => 2 * a 0 - 7 / 2
  | 1 => 2
  | _ => 0

def g2Coefficient (a : Fin 3 → ℝ) (k : Fin 4) : ℝ :=
  let c₂ := 4 * (a 0 + a 1 + a 2) - 33
  let c₁ := 251 / 4 + c₂ * (a 0 + a 1) -
    4 * (a 0 * a 1 + a 0 * a 2 + a 1 * a 2)
  match k.1 with
  | 0 => 4 * a 0 ^ 3 - 33 * a 0 ^ 2 +
      (251 / 4 : ℝ) * a 0 - 371 / 16
  | 1 => c₁
  | 2 => c₂
  | _ => 4

def coefficientMinor (a : Fin 3 → ℝ) (i j : Fin 4) : ℝ :=
  g1Coefficient a i * g2Coefficient a j -
    g1Coefficient a j * g2Coefficient a i

def g1Expansion (a : Fin 3 → ℝ) : Polynomial ℝ :=
  ∑ k : Fin 4,
    Polynomial.C (g1Coefficient a k) * factorialBasisPolynomial a k

def g2Expansion (a : Fin 3 → ℝ) : Polynomial ℝ :=
  ∑ k : Fin 4,
    Polynomial.C (g2Coefficient a k) * factorialBasisPolynomial a k

def factorialEvaluation (a : Fin 3 → ℝ) (k : Fin 4)
    (z : MvPolynomial (Fin 2) ℝ) : MvPolynomial (Fin 2) ℝ :=
  let c : ℝ → MvPolynomial (Fin 2) ℝ := MvPolynomial.C
  match k.1 with
  | 0 => 1
  | 1 => z - c (a 0)
  | 2 => (z - c (a 0)) * (z - c (a 1))
  | _ => (z - c (a 0)) * (z - c (a 1)) * (z - c (a 2))

def shiftedFactorialSchurMinor (a : Fin 3 → ℝ) (i j : Fin 4) :
    MvPolynomial (Fin 2) ℝ :=
  let c : ℝ → MvPolynomial (Fin 2) ℝ := MvPolynomial.C
  let x₁ := c 2 + MvPolynomial.X (0 : Fin 2)
  let x₂ := c 8 + MvPolynomial.X (1 : Fin 2)
  factorialEvaluation a i x₁ * factorialEvaluation a j x₂ -
    factorialEvaluation a j x₁ * factorialEvaluation a i x₂

def coefficientwiseNonnegative
    (P : MvPolynomial (Fin 2) ℝ) : Prop :=
  ∀ m : Fin 2 →₀ ℕ, 0 ≤ P.coeff m

def orderedNodes (a : Fin 3 → ℝ) : Prop :=
  a 0 ≤ a 1 ∧ a 1 ≤ a 2

/-- The exact two-column ordered factorial-basis architecture in the claim. -/
def factorialBasisArchitecture (a : Fin 3 → ℝ) : Prop :=
  orderedNodes a ∧
    g1Expansion a = g1Polynomial ∧
    g2Expansion a = g2Polynomial ∧
    (∀ i j : Fin 4, i.1 < j.1 →
      0 ≤ coefficientMinor a i j) ∧
    (∀ i j : Fin 4, i.1 < j.1 →
      coefficientwiseNonnegative (shiftedFactorialSchurMinor a i j))

/-- Claim 15715: the displayed two-column factorial basis cannot satisfy both
coefficient-minor nonnegativity families. -/
def claim15715 : Prop :=
  ¬ ∃ a : Fin 3 → ℝ, factorialBasisArchitecture a

end

end MathlibPlus.Open.NewResearch2.Q0002.Factorial15715
