import Mathlib

namespace MathlibPlus.Open.Analysis

open scoped BigOperators

noncomputable section

/-- The recursively defined polynomial family from the admitted rank-ten claim. -/
def p : Nat → Polynomial ℚ
  | 0 => 1
  | n + 1 =>
      Polynomial.X * (p n).derivative +
        (Polynomial.C (5 / 4 : ℚ) - Polynomial.X) * p n

/-- The nine derivatives used as rows of the alternant (with one-based indices). -/
def g (j : Fin 9) : Polynomial ℚ :=
  (p (2 * (j.val + 1))).derivative

def gEval (j i : Fin 9) : MvPolynomial (Fin 9) ℚ :=
  Polynomial.eval₂ (algebraMap ℚ (MvPolynomial (Fin 9) ℚ))
    (MvPolynomial.X i) (g j)

def factorialProduct : ℚ :=
  ∏ k ∈ Finset.range 9, (Nat.factorial k : ℚ)

def alternantNumerator : MvPolynomial (Fin 9) ℚ :=
  MvPolynomial.C factorialProduct * Matrix.det (fun i j => gEval j i)

def vandermondeDenominator : MvPolynomial (Fin 9) ℚ :=
  ∏ a ∈ (Finset.univ : Finset (Fin 9)),
    ∏ b ∈ Finset.univ.filter (fun b : Fin 9 => a < b),
      (MvPolynomial.X b - MvPolynomial.X a)

/-- Exact polynomial division, used only for the Vandermonde quotient. -/
noncomputable def exactQuotient
    {R : Type} [CommRing R] (numerator denominator : R) : R := by
  classical
  exact if h : denominator ∣ numerator then Classical.choose h else 0

def F9 : MvPolynomial (Fin 9) ℚ :=
  exactQuotient alternantNumerator vandermondeDenominator

def shiftedSquare (i : Fin 9) : ℚ :=
  ((i.val + 1 : ℕ) : ℚ) ^ 2

def uVar : MvPolynomial (Fin 10) ℚ := MvPolynomial.X 0

def xVar (i : Fin 9) : MvPolynomial (Fin 10) ℚ :=
  MvPolynomial.X (Fin.succ i)

def substitutedArgument (i : Fin 9) : MvPolynomial (Fin 10) ℚ :=
  (MvPolynomial.C (2 : ℚ) + uVar) * MvPolynomial.C (shiftedSquare i) + xVar i

def substitutedF9 : MvPolynomial (Fin 10) ℚ :=
  MvPolynomial.eval₂Hom (algebraMap ℚ (MvPolynomial (Fin 10) ℚ))
    substitutedArgument F9

def targetMonomial (s : Fin 9) (m : Fin 45) : Fin 10 →₀ ℕ :=
  Finsupp.single 0 m.val + Finsupp.single (Fin.succ s) 1

def targetCoefficient (s : Fin 9) (m : Fin 45) : ℚ :=
  MvPolynomial.coeff (targetMonomial s m) substitutedF9

/--
The rank-ten positivity claim: for each one-based variable index and each
power from zero through forty-four, the indicated coefficient is positive.
The pair of finite index ranges contains exactly 9 * 45 = 405 coefficients.
-/
def frontierAlphaRankR10LinearXPositivity : Prop :=
  ∀ s : Fin 9, ∀ m : Fin 45, 0 < targetCoefficient s m

end
end MathlibPlus.Open.Analysis
