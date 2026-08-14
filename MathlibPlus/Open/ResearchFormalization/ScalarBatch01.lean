import Mathlib

namespace MathlibPlus.Open.ResearchFormalization

noncomputable section
open scoped BigOperators

abbrev CoeffRing := MvPolynomial ℕ ℚ
abbrev RootedRing := Polynomial CoeffRing
abbrev ToricRing := MvPolynomial (Fin 2) ℚ

def xCoeff (k : ℕ) : CoeffRing := MvPolynomial.X k

def xPoly (k : ℕ) : RootedRing := Polynomial.C (xCoeff k)

def rootVariable : RootedRing := Polynomial.X

def rootedOperator (P : RootedRing) : RootedRing :=
  rootVariable * P +
    Polynomial.C (∑ k ∈ Finset.range (P.natDegree + 1), xCoeff k * P.coeff k)

def closedCorrection (P : RootedRing) : RootedRing :=
  rootedOperator P - rootVariable * P

def stableSubalgebra (T : Subalgebra ℚ RootedRing) : Prop :=
  ∀ P : RootedRing, P ∈ T → rootedOperator P ∈ T

def rootedFactorAlgebra : Subalgebra ℚ RootedRing :=
  sInf {T : Subalgebra ℚ RootedRing | stableSubalgebra T}

def zFree (P : RootedRing) : Prop :=
  ∀ k : ℕ, 0 < k → P.coeff k = 0

def scalarS : RootedRing := rootedOperator 1

def scalarE : RootedRing := rootedOperator scalarS

def scalarP : RootedRing := rootedOperator scalarE

def scalarC : RootedRing := rootedOperator (scalarS ^ 2)

def qStar (d : ℕ) : RootedRing :=
  rootedOperator (scalarS ^ (d - 1)) - scalarS ^ d

def delta (a : ℕ) : RootedRing :=
  xPoly (a - 1) - rootVariable ^ (a - 1) * xPoly 0

def commutatorK (a : RootedRing) (d : ℕ) : RootedRing :=
  a * rootedOperator (qStar d) - rootedOperator (a * qStar d)

def toricU : ToricRing := MvPolynomial.X 0

def toricV : ToricRing := MvPolynomial.X 1

def toricSpecialization : CoeffRing →+* ToricRing :=
  MvPolynomial.eval₂Hom (algebraMap ℚ ToricRing)
    (fun k => toricU * toricV ^ (k + 1))

def rankOneToricIdeal : Ideal CoeffRing :=
  Ideal.comap toricSpecialization (⊥ : Ideal ToricRing)

def claim_23268 : Prop :=
  stableSubalgebra rootedFactorAlgebra ∧
    (1 : RootedRing) ∈ rootedFactorAlgebra ∧
    (∀ T : Subalgebra ℚ RootedRing,
      stableSubalgebra T → rootedFactorAlgebra ≤ T) ∧
    (∀ P : RootedRing,
      closedCorrection P =
        Polynomial.C (∑ k ∈ Finset.range (P.natDegree + 1),
          xCoeff k * P.coeff k))

def claim_23269 : Prop :=
  2 * scalarS * scalarP - scalarS * scalarC - scalarE ^ 2 -
      rootedOperator scalarC + rootedOperator (scalarS ^ 3) =
    Polynomial.C (xCoeff 0 * xCoeff 2 - xCoeff 1 ^ 2)

def claim_23274 : Prop :=
  ∀ d : ℕ, 2 ≤ d →
    qStar d =
      ∑ j ∈ Finset.Icc 1 (d - 1),
        (Nat.choose (d - 1) j : RootedRing) *
          xPoly 0 ^ (d - 1 - j) *
            (xPoly j - rootVariable ^ j * xPoly 0)

def claim_23275 : Prop :=
  ∀ d : ℕ, 2 ≤ d →
    closedCorrection (qStar d) = 0 ∧
      rootedOperator (qStar d) = rootVariable * qStar d

def claim_23276 : Prop :=
  (∀ (a : RootedRing), a ∈ rootedFactorAlgebra →
    ∀ d : ℕ, 2 ≤ d →
      zFree (commutatorK a d) ∧ commutatorK a d ∈ rootedFactorAlgebra) ∧
    commutatorK scalarS 2 = Polynomial.C (xCoeff 0 * xCoeff 2 - xCoeff 1 ^ 2)

def claim_23277 : Prop :=
  (∀ P : RootedRing,
    toricSpecialization ((closedCorrection P).coeff 0) =
      toricU * toricV * Polynomial.eval₂ toricSpecialization toricV P) ∧
    (∀ d : ℕ, 2 ≤ d →
      Polynomial.eval₂ toricSpecialization toricV (qStar d) = 0) ∧
    (∀ (a : RootedRing), a ∈ rootedFactorAlgebra →
      ∀ d : ℕ, 2 ≤ d →
        zFree (commutatorK a d) ∧
          (commutatorK a d).coeff 0 ∈ rankOneToricIdeal)

def claim_23282 : Prop :=
  (∀ a : ℕ, 2 ≤ a →
    closedCorrection (delta a) = 0 ∧
      rootedOperator (delta a) = rootVariable * delta a) ∧
    (∀ d : ℕ, 2 ≤ d →
      qStar d =
        ∑ j ∈ Finset.Icc 1 (d - 1),
          (Nat.choose (d - 1) j : RootedRing) *
            xPoly 0 ^ (d - 1 - j) * delta (j + 1)) ∧
    (∀ d : ℕ, 2 ≤ d → Nat.choose (d - 1) (d - 1) = 1) ∧
    qStar 2 = delta 2 ∧
    (∀ E : RootedRing,
      rootedOperator E = rootVariable * E →
        xPoly 0 * E = scalarS * E - rootedOperator E) ∧
    (∀ (q a : ℕ), 2 ≤ a →
      xPoly 0 ^ q * delta a ∈ rootedFactorAlgebra ∧
        rootedOperator (xPoly 0 ^ q * delta a) =
          rootVariable * (xPoly 0 ^ q * delta a))

end

end MathlibPlus.Open.ResearchFormalization
