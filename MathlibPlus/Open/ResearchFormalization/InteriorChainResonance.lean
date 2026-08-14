import Mathlib

namespace MathlibPlus.Open.ResearchFormalization

noncomputable section

abbrev Polynomial := MvPolynomial (Fin 9) ℚ

def aVar : Polynomial := MvPolynomial.X 0

def bVar : Polynomial := MvPolynomial.X 1

def mVar : Polynomial := MvPolynomial.X 2

def nVar : Polynomial := MvPolynomial.X 3

def cVar : Polynomial := MvPolynomial.X 4

def dVar : Polynomial := MvPolynomial.X 5

def xVar : Polynomial := MvPolynomial.X 6

def yVar : Polynomial := MvPolynomial.X 7

def zVar : Polynomial := MvPolynomial.X 8

def shiftedA : Polynomial := aVar - 1

def shiftedB : Polynomial := bVar - 1

def shiftedM : Polynomial := mVar - 1

def shiftedN : Polynomial := nVar - 1

def shiftedC : Polynomial := cVar - 1

def shiftedD : Polynomial := dVar - 1

def sigmaL : Polynomial := shiftedB - shiftedA - xVar

def sigmaR : Polynomial := shiftedD - shiftedC + zVar

def R_bend : Polynomial := xVar * yVar * zVar * (xVar - yVar) * (yVar - zVar)

def R_leaf : Polynomial := xVar * yVar * zVar * (shiftedM - shiftedN) * (xVar - yVar + zVar)

def R_quad : Polynomial :=
  xVar * yVar * zVar * (xVar ^ 2 - xVar * zVar - yVar ^ 2 + zVar ^ 2)

def V_bend : Polynomial := sigmaL * sigmaR * R_bend

def V_leaf : Polynomial := sigmaL * sigmaR * R_leaf

def V_quad : Polynomial := sigmaL * sigmaR * R_quad

def residualSpan : Submodule ℚ Polynomial :=
  Submodule.span ℚ ({R_bend, R_leaf, R_quad} : Set Polynomial)

def endpointCore : Polynomial := sigmaL * sigmaR

def endpointMultiply : Polynomial →ₗ[ℚ] Polynomial :=
  { toFun := fun p => endpointCore * p
    map_add' := by
      intro p q
      exact mul_add _ _ _
    map_smul' := by
      intro r p
      simp [Algebra.smul_def, mul_assoc, mul_comm, mul_left_comm] }

def R_chain : Submodule ℚ Polynomial :=
  Submodule.span ℚ ({V_bend, V_leaf, V_quad} : Set Polynomial)

def endpointScaledSpan : Submodule ℚ Polynomial :=
  Submodule.map endpointMultiply residualSpan

def interiorChainResonanceModule : Prop :=
  R_chain = endpointScaledSpan

end

end MathlibPlus.Open.ResearchFormalization
