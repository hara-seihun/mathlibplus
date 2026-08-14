import Mathlib

namespace MathlibPlus.Open.Algebra

noncomputable section

abbrev QuadraticGeneratorRing := MvPolynomial (Fin 4) ℚ

namespace QuadraticGeneratorSyzygy

local notation "R" => QuadraticGeneratorRing

/-- The four intrinsic polynomial coordinates from the admitted residual data. -/
def X : R := MvPolynomial.X 0

def Y : R := MvPolynomial.X 1

def Z : R := MvPolynomial.X 2

def η : R := MvPolynomial.X 3

/-- The three admitted residual quadratic survivors. -/
def g₁ : R := (X - Y) * (Y - Z)

def g₂ : R := η * (X - Y + Z)

def g₃ : R := X ^ 2 - X * Z - Y ^ 2 + Z ^ 2

/-- The ordered family of residual quadratic generators. -/
def quadraticGenerators : Fin 3 → R := ![g₁, g₂, g₃]

/--
The admitted quadratic-generator syzygy, together with its stated consequence:
the three residual quadratics are not a free polynomial generating family.
-/
def quadraticGeneratorSyzygy : Prop :=
  (-3 * η * g₁ + (-X + 2 * Y - Z) * g₂ + η * g₃ = 0) ∧
    ¬ LinearIndependent R quadraticGenerators

end QuadraticGeneratorSyzygy

end

end MathlibPlus.Open.Algebra
