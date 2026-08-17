import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.BatchR3735Claim50230

noncomputable section
open scoped BigOperators

abbrev Coeff := FractionRing (MvPolynomial (Fin 2) ℚ)
abbrev WPoly := Polynomial Coeff
abbrev Row := Fin 3 → WPoly

private def u : Coeff :=
  algebraMap (MvPolynomial (Fin 2) ℚ) Coeff (MvPolynomial.X 0)

private def rho : Coeff :=
  algebraMap (MvPolynomial (Fin 2) ℚ) Coeff (MvPolynomial.X 1)

inductive RootedContext where
  | node (children : List RootedContext) : RootedContext

private def contextChildren : RootedContext → List RootedContext
  | .node children => children

private def contextOrder : RootedContext → ℕ
  | .node children => 1 + (children.map contextOrder).sum

structure ContextData where
  prime : RootedContext → WPoly
  subleading : RootedContext → Coeff

private def childProduct (D : ContextData) (C : RootedContext) : WPoly :=
  ((contextChildren C).map D.prime).prod

private def childSubleadingSum (D : ContextData) (C : RootedContext) : Coeff :=
  ((contextChildren C).map D.subleading).sum

private def w : WPoly := Polynomial.X

private def contextPrimeRecursion (D : ContextData) (C : RootedContext) : Prop :=
  D.prime C = Polynomial.C u * (Polynomial.C (u + rho)) ^ (contextOrder C - 1) +
    w * childProduct D C

private def childOrderCondition (C : RootedContext) : Prop :=
  ((contextChildren C).map contextOrder).sum = contextOrder C - 1

private def monicExpansion (D : ContextData) (C : RootedContext) : Prop :=
  (D.prime C).natDegree = contextOrder C ∧
    (D.prime C).leadingCoeff = 1 ∧
    (D.prime C).coeff (contextOrder C - 1) = D.subleading C

private def contextDataAt (D : ContextData) (C : RootedContext) : Prop :=
  contextPrimeRecursion D C ∧
    childOrderCondition C ∧
    D.subleading C = childSubleadingSum D C ∧
    (∀ X ∈ contextChildren C, monicExpansion D X)

private def contextVector (D : ContextData) (C : Fin 3 → RootedContext) : Row :=
  fun i => D.prime (C i)

private def subleadingVector (D : ContextData) (C : Fin 3 → RootedContext) : Fin 3 → Coeff :=
  fun i => D.subleading (C i)

private def cross (f q : Row) : Row :=
  ![f 1 * q 2 - f 2 * q 1,
    f 2 * q 0 - f 0 * q 2,
    f 0 * q 1 - f 1 * q 0]

private def rowScale (p : WPoly) (r : Row) : Row :=
  fun i => p * r i

private def rowAdd (r s : Row) : Row :=
  fun i => r i + s i

private def rowSub (r s : Row) : Row :=
  fun i => r i - s i

private def constantRow : Row := fun _ => 1

private def deltaMode (f : Row) : Row :=
  cross f constantRow

private def xiMode (f : Row) (b : Fin 3 → Coeff) : Row :=
  cross f (fun i => w + Polynomial.C (b i))

private def contextTriangle (f : Row) : Row :=
  cross f constantRow

private def pairXi (D : ContextData) (C E : RootedContext) : WPoly :=
  D.prime C * (w + Polynomial.C (D.subleading E)) -
    D.prime E * (w + Polynomial.C (D.subleading C))

private def pairTelescopeData (D : ContextData) (C E : RootedContext)
    (theta : RootedContext → WPoly) : Prop :=
  let deltaB := D.subleading E - D.subleading C
  let GC := childProduct D C
  let GE := childProduct D E
  (D.subleading E - D.subleading C =
      childSubleadingSum D E - childSubleadingSum D C) ∧
    (GC - GE = (w - Polynomial.C rho) * (theta C - theta E)) ∧
    pairXi D C E =
      (Polynomial.C u * (Polynomial.C (u + rho)) ^ (contextOrder C - 1)) *
          Polynomial.C deltaB +
        w * (w + Polynomial.C (D.subleading E)) *
            (w - Polynomial.C rho) * (theta C - theta E) +
        w * Polynomial.C deltaB * GE

private def pairwiseXiSignedSum (D : ContextData) (C : Fin 3 → RootedContext) : Row :=
  ![pairXi D (C 1) (C 2),
    pairXi D (C 2) (C 0),
    pairXi D (C 0) (C 1)]

structure SourceData where
  a : ℕ
  contexts : Fin 3 → RootedContext
  data : ContextData
  q : Row
  A : Row
  ell : Coeff
  tau : Row
  theta : RootedContext → WPoly
  delta : Fin 3 → ℤ

private def sourceContexts (S : SourceData) : Prop :=
  (∀ i : Fin 3, contextOrder (S.contexts i) = S.a) ∧
    (∀ i j : Fin 3, i ≠ j → S.contexts i ≠ S.contexts j) ∧
    4 ≤ S.a ∧
    (∀ i : Fin 3, contextDataAt S.data (S.contexts i))

private def degreeAtMost (p : WPoly) (bound : ℤ) : Prop :=
  p = 0 ∨ (p ≠ 0 ∧ (p.natDegree : ℤ) ≤ bound)

private def qDegreeBound (S : SourceData) (q : Row) : Prop :=
  ∀ i : Fin 3, degreeAtMost (q i) ((S.a : ℤ) - 3)

private def factorization (S : SourceData) (q : Row) : Prop :=
  ∀ i : Fin 3,
    S.A i = w * (w - Polynomial.C rho) *
      (S.ell • S.tau i + cross (contextVector S.data S.contexts) q i)

private def admissibleQ (S : SourceData) (q : Row) : Prop :=
  qDegreeBound S q ∧ factorization S q

private def uniqueCarrierRow (S : SourceData) : Prop :=
  admissibleQ S S.q ∧
    ∀ q' : Row, admissibleQ S q' → q' = S.q

private def physicalCarrierBound (S : SourceData) : Prop :=
  ∀ i : Fin 3,
    degreeAtMost
      (S.A i / (w * (w - Polynomial.C rho)))
      ((S.a : ℤ) + S.delta i - 4) ∧
    (S.a : ℤ) + S.delta i - 4 ≤ 2 * (S.a : ℤ) - 5 ∧
    degreeAtMost (S.ell • S.tau i) ((S.a : ℤ) - 2)

private def sourceS1S5S7 (S : SourceData) : Prop :=
  sourceContexts S ∧
    uniqueCarrierRow S ∧
    physicalCarrierBound S ∧
    (∀ i j : Fin 3, i ≠ j →
      pairTelescopeData S.data (S.contexts i) (S.contexts j) S.theta)

private def normalizedResidual (S : SourceData) (alpha gamma : Coeff)
    (qbar : Row) : Prop :=
  (∀ i : Fin 3,
    S.q i =
      Polynomial.C alpha * w ^ (S.a - 4) *
          (w + Polynomial.C (S.data.subleading (S.contexts i))) +
        Polynomial.C gamma * w ^ (S.a - 4) + qbar i) ∧
    (∀ i : Fin 3, degreeAtMost (qbar i) ((S.a : ℤ) - 5))

private def alphaMode (S : SourceData) : Row :=
  rowScale (w ^ (S.a - 4))
    (xiMode (contextVector S.data S.contexts)
      (subleadingVector S.data S.contexts))

private def gammaMode (S : SourceData) : Row :=
  rowScale (w ^ (S.a - 4))
    (deltaMode (contextVector S.data S.contexts))

private def modeSpan (S : SourceData) : Submodule Coeff Row :=
  Submodule.span Coeff {alphaMode S, gammaMode S}

private def moduloModes (S : SourceData) (r s : Row) : Prop :=
  rowSub r s ∈ modeSpan S

private def modeDecomposition (S : SourceData) (alpha gamma : Coeff)
    (qbar : Row) : Prop :=
  cross (contextVector S.data S.contexts) S.q =
      rowAdd (cross (contextVector S.data S.contexts) qbar)
        (rowAdd
          (rowScale (Polynomial.C alpha * w ^ (S.a - 4))
            (xiMode (contextVector S.data S.contexts)
              (subleadingVector S.data S.contexts)))
          (rowScale (Polynomial.C gamma * w ^ (S.a - 4))
            (deltaMode (contextVector S.data S.contexts))))

private def modeIdentifications (S : SourceData) : Prop :=
  deltaMode (contextVector S.data S.contexts) =
      contextTriangle (contextVector S.data S.contexts) ∧
    xiMode (contextVector S.data S.contexts)
        (subleadingVector S.data S.contexts) =
      pairwiseXiSignedSum S.data S.contexts

/-- Claim 50230: after the S5 context-triangle and S7 pair-telescope modes
are removed, the uniquely normalized residual `f × q̄` is the only remaining
potentially primitive mixed row. -/
def contextModesAndMixedResidual_claim50230 : Prop :=
  ∀ S : SourceData,
    sourceS1S5S7 S →
      ∃ alpha gamma : Coeff, ∃ qbar : Row,
        normalizedResidual S alpha gamma qbar ∧
          modeDecomposition S alpha gamma qbar ∧
          modeIdentifications S ∧
          moduloModes S
            (cross (contextVector S.data S.contexts) S.q)
            (cross (contextVector S.data S.contexts) qbar) ∧
          (∀ i : Fin 3,
            degreeAtMost
              (cross (contextVector S.data S.contexts) S.q i)
              (2 * (S.a : ℤ) - 5)) ∧
          (∀ alpha' gamma' : Coeff, ∀ qbar' : Row,
            normalizedResidual S alpha' gamma' qbar' ∧
              modeDecomposition S alpha' gamma' qbar' →
              alpha' = alpha ∧ gamma' = gamma ∧ qbar' = qbar)

end
end MathlibPlus.Open.ResearchFormalization.BatchR3735Claim50230
