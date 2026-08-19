import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R3735Claim50229

noncomputable section

abbrev Coeff := FractionRing (MvPolynomial (Fin 2) ℚ)
abbrev WPoly := Polynomial Coeff

private def u : Coeff :=
  algebraMap (MvPolynomial (Fin 2) ℚ) Coeff (MvPolynomial.X 0)

private def rho : Coeff :=
  algebraMap (MvPolynomial (Fin 2) ℚ) Coeff (MvPolynomial.X 1)

inductive RootedContext where
  | node (children : List RootedContext) : RootedContext

def contextChildren : RootedContext → List RootedContext
  | .node children => children

def contextOrder : RootedContext → ℕ
  | .node children => 1 + (children.map contextOrder).sum

structure ContextData where
  prime : RootedContext → WPoly
  subleading : RootedContext → Coeff

def childProduct (D : ContextData) (C : RootedContext) : WPoly :=
  ((contextChildren C).map D.prime).prod

def childSubleadingSum (D : ContextData) (C : RootedContext) : Coeff :=
  ((contextChildren C).map D.subleading).sum

private def w : WPoly := Polynomial.X

def contextPrimeRecursion (D : ContextData) (C : RootedContext) : Prop :=
  D.prime C = Polynomial.C u * (Polynomial.C (u + rho)) ^ (contextOrder C - 1) +
    w * childProduct D C

def childOrderCondition (C : RootedContext) : Prop :=
  ((contextChildren C).map contextOrder).sum = contextOrder C - 1

def monicExpansion (D : ContextData) (C : RootedContext) : Prop :=
  (D.prime C).natDegree = contextOrder C ∧
    (D.prime C).leadingCoeff = 1 ∧
    (D.prime C).coeff (contextOrder C - 1) = D.subleading C

def contextDataAt (D : ContextData) (C : RootedContext) : Prop :=
  contextPrimeRecursion D C ∧
    childOrderCondition C ∧
    D.subleading C = childSubleadingSum D C ∧
    (∀ X ∈ contextChildren C, monicExpansion D X)

def pairXi (D : ContextData) (C E : RootedContext) : WPoly :=
  D.prime C * (w + Polynomial.C (D.subleading E)) -
    D.prime E * (w + Polynomial.C (D.subleading C))

/-- The three displayed summands, with the subleading and divided factors
retained as strict-proper-child context data. -/
def properChildPairTelescope (D : ContextData) (C E : RootedContext)
    (theta : RootedContext → WPoly) : Prop :=
  let deltaB := D.subleading E - D.subleading C
  let GC := childProduct D C
  let GE := childProduct D E
  deltaB = childSubleadingSum D E - childSubleadingSum D C ∧
    GC - GE = (w - Polynomial.C rho) * (theta C - theta E) ∧
    pairXi D C E =
      (Polynomial.C u * (Polynomial.C (u + rho)) ^ (contextOrder C - 1)) *
          Polynomial.C deltaB +
        w * (w + Polynomial.C (D.subleading E)) *
            (w - Polynomial.C rho) * (theta C - theta E) +
        w * Polynomial.C deltaB * GE

/-- Claim 50229: the pair component has the exact three-term proper-child
context telescope, including the S6 child-subleading difference and the S7
strict-proper-child divided factor. -/
def pairComponentProperChildTelescope_claim50229 : Prop :=
  ∀ (C D : RootedContext) (data : ContextData)
    (theta : RootedContext → WPoly),
    contextOrder C = contextOrder D →
      C ≠ D →
        contextDataAt data C →
          contextDataAt data D →
            childProduct data C - childProduct data D =
              (w - Polynomial.C rho) * (theta C - theta D) →
              properChildPairTelescope data C D theta

end

end MathlibPlus.Open.ResearchFormalization.R3735Claim50229
