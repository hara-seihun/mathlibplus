import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.BatchD0101

noncomputable section

abbrev ThreeArmPolynomial := MvPolynomial (Fin 3) ℚ

def armVariable (i : Fin 3) : ThreeArmPolynomial := MvPolynomial.X i

def A : ThreeArmPolynomial := armVariable 0

def B : ThreeArmPolynomial := armVariable 1

def M : ThreeArmPolynomial := armVariable 2

def variableExponent (i : Fin 3) : Fin 3 →₀ ℕ := Finsupp.single i 1

def specializeAtZero (i : Fin 3) (F : ThreeArmPolynomial) : ThreeArmPolynomial :=
  ∑ e ∈ F.support, if e i = 0 then MvPolynomial.monomial e (MvPolynomial.coeff e F) else 0

def bulkLowering (i : Fin 3) (F : ThreeArmPolynomial) : ThreeArmPolynomial :=
  ∑ e ∈ F.support, if e i = 0 then 0 else
    MvPolynomial.monomial (e - variableExponent i) (MvPolynomial.coeff e F)

def facetCoefficient (i : Fin 3) (F : ThreeArmPolynomial) : ThreeArmPolynomial :=
  ∑ e ∈ F.support, if e i = 1 then
    MvPolynomial.monomial (e - variableExponent i) (MvPolynomial.coeff e F) else 0

def sameStratumEquations (F : ThreeArmPolynomial) : Prop :=
  (∑ i : Fin 3, bulkLowering i F = 0) ∧
    (∑ i : Fin 3, facetCoefficient i F = 0)

end

end MathlibPlus.Open.ResearchFormalization.BatchD0101
