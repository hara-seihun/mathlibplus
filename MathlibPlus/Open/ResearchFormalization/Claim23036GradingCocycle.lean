import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.Claim23036

open scoped BigOperators

noncomputable section

abbrev ScalarFactorPolynomial := MvPolynomial ℕ ℚ

def zVariable : ScalarFactorPolynomial :=
  MvPolynomial.X 0

def xVariable (k : ℕ) : ScalarFactorPolynomial :=
  MvPolynomial.X (k + 1)

def scalarRootClosure (P : ScalarFactorPolynomial) : ScalarFactorPolynomial :=
  zVariable * P +
    ∑ exponent ∈ P.support,
      xVariable (exponent 0) *
        MvPolynomial.monomial (exponent.erase 0)
          (MvPolynomial.coeff exponent P)

def singletonFactor : ScalarFactorPolynomial :=
  scalarRootClosure 1

def edgeFactor : ScalarFactorPolynomial :=
  scalarRootClosure singletonFactor

def pathFactor : ScalarFactorPolynomial :=
  scalarRootClosure edgeFactor

def starFactor : ScalarFactorPolynomial :=
  scalarRootClosure (singletonFactor * singletonFactor)

def pathForestFactor : ScalarFactorPolynomial :=
  singletonFactor * edgeFactor

def variableWeight (i : ℕ) : ℕ :=
  if i = 0 then 1 else i

def monomialWeight (m : ℕ →₀ ℕ) : ℕ :=
  m.sum (fun i exponent => exponent * variableWeight i)

def gradingScale (t : ℚ) (P : ScalarFactorPolynomial) :
    ScalarFactorPolynomial :=
  ∑ exponent ∈ P.support,
    MvPolynomial.monomial exponent
      (t ^ monomialWeight exponent * MvPolynomial.coeff exponent P)

def coordinateExponent : Fin 3 → ℕ →₀ ℕ :=
  ![Finsupp.single 0 1 + Finsupp.single 3 1,
    Finsupp.single 0 2 + Finsupp.single 2 1,
    Finsupp.single 4 1]

def coefficientPolynomial : Fin 3 → ScalarFactorPolynomial :=
  ![pathFactor, pathForestFactor, starFactor]

def coefficientMatrix : Matrix (Fin 3) (Fin 3) ℚ :=
  fun coordinate polynomial =>
    MvPolynomial.coeff (coordinateExponent coordinate)
      (coefficientPolynomial polynomial)

def scalarPolynomial (q : ℚ) : ScalarFactorPolynomial :=
  MvPolynomial.C q

def oneSidedCocycleDefect (t : ℚ) :
    TensorProduct ℚ ScalarFactorPolynomial ScalarFactorPolynomial :=
  TensorProduct.tmul ℚ singletonFactor
    (scalarPolynomial (1 + t - 2 * t ^ 2) * pathFactor +
      scalarPolynomial (t ^ 2 - 2 * t) * pathForestFactor +
      scalarPolynomial (t ^ 2) * starFactor)

def gradingScaledOneSidedCocycleNoGo : Prop :=
  Matrix.det coefficientMatrix = 3 ∧
    LinearIndependent ℚ coefficientPolynomial ∧
    ∀ t : ℚ, oneSidedCocycleDefect t ≠ 0

end

end MathlibPlus.Open.ResearchFormalization.Claim23036
