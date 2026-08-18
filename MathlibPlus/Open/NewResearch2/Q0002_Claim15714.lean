import MathlibPlus.Open.NewResearch2.Q0002_Factorial15716

namespace MathlibPlus.Open.NewResearch2.Q0002.Claim15714

noncomputable section

abbrev ShiftPolynomial := MvPolynomial (Fin 2) ℝ

def squareFactorialP3 (z : ShiftPolynomial) : ShiftPolynomial :=
  z * (z - MvPolynomial.C 2) * (z - MvPolynomial.C 8)

def shiftedSquareFactorialMinor : ShiftPolynomial :=
  squareFactorialP3
      (MvPolynomial.C 8 + MvPolynomial.X (1 : Fin 2)) -
    squareFactorialP3
      (MvPolynomial.C 2 + MvPolynomial.X (0 : Fin 2))

def coefficientwiseNonnegative (P : ShiftPolynomial) : Prop :=
  ∀ m : Fin 2 →₀ ℕ, 0 ≤ P.coeff m

/-- Claim 15714: the square-factorial shifted minor for exponent set `(0,3)`
at shifts `(2+Y₁,8+Y₂)` has coefficient `-1` at `Y₁^3`, so it is not
coefficientwise nonnegative. -/
def claim15714 : Prop :=
  shiftedSquareFactorialMinor.coeff
      (Finsupp.single (0 : Fin 2) 3) = -1 ∧
    ¬coefficientwiseNonnegative shiftedSquareFactorialMinor

end

end MathlibPlus.Open.NewResearch2.Q0002.Claim15714
