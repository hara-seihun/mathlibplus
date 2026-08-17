import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.Claim1710

noncomputable section

abbrev BatchPolynomial := MvPolynomial (Fin 2) ℚ

def bVariable : BatchPolynomial := MvPolynomial.X 0

def mVariable : BatchPolynomial := MvPolynomial.X 1

def rationalConstant (x : ℚ) : BatchPolynomial := MvPolynomial.C x

def risingPolynomial (x : BatchPolynomial) (k : ℕ) : BatchPolynomial :=
  Finset.prod (Finset.range k) (fun i => x + rationalConstant (i : ℚ))

def coefficientwiseNonnegative (p : BatchPolynomial) : Prop :=
  ∀ c : Fin 2 →₀ ℕ, 0 ≤ p.coeff c

def coefficientwisePositive (p : BatchPolynomial) : Prop :=
  ∀ c : Fin 2 →₀ ℕ, c ∈ p.support → 0 < p.coeff c

/-- The factor `G_n(m)` in the admitted closed form. -/
def G (n : ℕ) : BatchPolynomial :=
  (mVariable + rationalConstant (2 * (n : ℚ))) *
    risingPolynomial (mVariable + rationalConstant 1) (n - 2) *
    rationalConstant
      (1 / (((n + 1 : ℕ) : ℚ) * (Nat.factorial n : ℚ)))

/-- The factor `J_n(m,b)` in the admitted closed form. -/
def J (n : ℕ) : BatchPolynomial :=
  let N : ℚ := n
  rationalConstant (8 * (N + 1)) *
      (mVariable + rationalConstant (N - 1)) * bVariable ^ 3 +
    rationalConstant 4 *
      (rationalConstant (2 * N + 3) * mVariable ^ 2 +
        rationalConstant (4 * N ^ 2 + 5 * N) * mVariable +
        rationalConstant (2 * N ^ 3 + 3 * N ^ 2 - 2 * N - 3)) * bVariable ^ 2 +
    (rationalConstant (3 * N + 5) * mVariable ^ 3 +
      rationalConstant (9 * N ^ 2 + 13 * N + 4) * mVariable ^ 2 +
      rationalConstant (9 * N ^ 3 + 13 * N ^ 2 - N - 7) * mVariable +
      rationalConstant (3 * N ^ 4 + 5 * N ^ 3 - N ^ 2 - 5 * N - 2)) * bVariable +
    rationalConstant (1 / 6) *
      (mVariable + rationalConstant (N - 1)) *
      (mVariable + rationalConstant (N + 2)) *
      (rationalConstant (2 * N + 5) * mVariable ^ 2 +
        rationalConstant (4 * N ^ 2 + 6 * N - 1) * mVariable +
        rationalConstant (2 * N ^ 3 + 4 * N ^ 2 - 10 * N - 12))

/-- The correction `L_n(m,b)=G_n(m)J_n(m,b)`. -/
def L (n : ℕ) : BatchPolynomial := G n * J n

/-- Claim 1710: for `n ≥ 3`, every coefficient occurring in `J_n` is
positive and the displayed correction has nonnegative coefficients. -/
def claim1710_positiveCorrectionClosedForm : Prop :=
  ∀ n : ℕ, 3 ≤ n →
    coefficientwisePositive (J n) ∧ coefficientwiseNonnegative (L n)

end

end MathlibPlus.Open.ResearchFormalization.Claim1710
