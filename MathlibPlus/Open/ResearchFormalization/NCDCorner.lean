import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.NCDCorner

noncomputable section

abbrev A := MvPolynomial (Fin 5) ℚ

def c₂ : A := MvPolynomial.X 0
def c₃ : A := MvPolynomial.X 1
def q : A := MvPolynomial.X 2
def t : A := MvPolynomial.X 3
def u : A := MvPolynomial.X 4

abbrev R : Type := A ⧸ Ideal.span ({u - t ^ 2} : Set A)

def quotientMapA : A →+* R := Ideal.Quotient.mk _

def rc₂ : R := quotientMapA c₂
def rc₃ : R := quotientMapA c₃

abbrev S := Polynomial R

def s : S := Polynomial.X

def cornerRelation : S :=
  2 * s ^ 3 - 3 * Polynomial.C rc₂ * s + 2 * Polynomial.C rc₃

abbrev B : Type := S ⧸ Ideal.span ({cornerRelation} : Set S)

instance cornerIdealIsTwoSided :
    (Ideal.span ({cornerRelation} : Set S)).IsTwoSided :=
  Ideal.instIsTwoSided_1 (α := S)
    (Ideal.span ({cornerRelation} : Set S))

def quotientMapS : S →+* B :=
  Ideal.Quotient.mk (Ideal.span ({cornerRelation} : Set S))

def cornerS : B := quotientMapS s

def cornerBasisVector (i : Fin 3) : B :=
  if i = 0 then 1 else if i = 1 then cornerS else cornerS ^ 2

def exact_corner_is_free_rank_three : Prop :=
  ∃ b : Module.Basis (Fin 3) R B, ∀ i, b i = cornerBasisVector i


def standardBasis (i : Fin 11) : Fin 11 → A :=
  fun j => if j = i then 1 else 0

def oneThird : A := algebraMap ℚ A (1 / 3)

def redundant_visible_generators : Prop :=
  (u - t ^ 2) • standardBasis 5 =
    oneThird •
      ((u - t ^ 2) • (-(t • standardBasis 3) + (3 : A) • standardBasis 5) +
        (t * (u - t ^ 2)) • standardBasis 3) ∧
  (u - t ^ 2) • standardBasis 9 =
    oneThird •
      ((u - t ^ 2) • (-(t • standardBasis 7) + (3 : A) • standardBasis 9) +
        (t * (u - t ^ 2)) • standardBasis 7)

end
end MathlibPlus.Open.ResearchFormalization.NCDCorner
