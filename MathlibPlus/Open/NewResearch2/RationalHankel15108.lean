import Mathlib
import MathlibPlus.Open.NewResearch2.RationalHankel15104_15107

open scoped BigOperators
open Polynomial

namespace MathlibPlus.Open.NewResearch2.RationalHankel15108

noncomputable section

/-- Iterated differentiation for the normalized Hermite jets. -/
def iteratedPolynomialDerivative : ℕ → Polynomial ℂ → Polynomial ℂ
  | 0, p => p
  | k + 1, p => iteratedPolynomialDerivative k (Polynomial.derivative p)

/-- The normalized derivative jet of a numerator polynomial at one root. -/
def normalizedHermiteJet (p : Polynomial ℂ) (z : ℂ) (k : ℕ) : ℂ :=
  Polynomial.eval z (iteratedPolynomialDerivative k p) / (Nat.factorial k : ℂ)

/-- The vector rational function represented in the fraction field of the
polynomial ring.  The numerator and denominator are the actual carriers of
Claims 15103 and 15108, rather than arbitrary functions. -/
def representedRationalFunction {d : ℕ}
    (P : Fin d → Polynomial ℂ) (Q : Polynomial ℂ) :
    Fin d → FractionRing (Polynomial ℂ) :=
  fun i =>
    algebraMap (Polynomial ℂ) (FractionRing (Polynomial ℂ)) (P i) /
      algebraMap (Polynomial ℂ) (FractionRing (Polynomial ℂ)) Q

/-- The proper vector-rational hypotheses carried by the admitted model. -/
def properVectorRationalModel {d : ℕ}
    (P : Fin d → Polynomial ℂ) (Q : Polynomial ℂ) : Prop :=
  Q ≠ 0 ∧ Q.coeff 0 = 1 ∧
    (∀ i : Fin d, (P i).degree < Q.degree)

/-- Cancellation in the minimal recurrence, stated by comparing the nominal
recurrence, the factor being canceled, and the residual minimal recurrence.
It deliberately permits a reciprocal node to remain with lower multiplicity in
the residual polynomial. -/
def minimalRecurrenceCancellation
    (S Q Qstar : Polynomial ℂ) : Prop :=
  ∀ lam : ℂ,
    Polynomial.rootMultiplicity lam
        (MathlibPlus.Open.NewResearch2.RationalHankelStructure.reciprocalPolynomial S) +
      Polynomial.rootMultiplicity lam
        (MathlibPlus.Open.NewResearch2.RationalHankelStructure.reciprocalPolynomial Qstar) ≤
    Polynomial.rootMultiplicity lam
      (MathlibPlus.Open.NewResearch2.RationalHankelStructure.reciprocalPolynomial Q)

/-- Dividing numerator and denominator by the same divisor leaves every
represented component unchanged in the fraction field. -/
def divisionLeavesRationalFunctionUnchanged {d : ℕ}
    (P : Fin d → Polynomial ℂ) (Q S : Polynomial ℂ) : Prop :=
  ∀ i : Fin d,
    representedRationalFunction P Q i =
      representedRationalFunction (fun j => P j / S) (Q / S) i

/-- Claim 15108: for every divisor of the nominal denominator, common-gcd
 divisibility, numerator divisibility, vanishing of all normalized Hermite
jets through the divisor's root multiplicities, the corresponding drop in the
minimal recurrence multiplicities, and unchanged rational-function division
are equivalent. -/
def claim_15108 : Prop :=
  ∀ (d : ℕ) (P : Fin d → Polynomial ℂ) (Q : Polynomial ℂ),
    properVectorRationalModel P Q →
      let G :=
        MathlibPlus.Open.NewResearch2.RationalHankelStructure.commonFroissartDivisor
          P Q
      let Qstar :=
        MathlibPlus.Open.NewResearch2.RationalHankelStructure.reducedDenominator P Q
      ∀ S : Polynomial ℂ, S ∣ Q →
        (S ∣ G ↔ ∀ i : Fin d, S ∣ P i) ∧
          (S ∣ G ↔
            ∀ (i : Fin d) (z : ℂ) (k : ℕ),
              k < Polynomial.rootMultiplicity z S →
                normalizedHermiteJet (P i) z k = 0) ∧
          (S ∣ G ↔ minimalRecurrenceCancellation S Q Qstar) ∧
          (S ∣ G ↔ divisionLeavesRationalFunctionUnchanged P Q S)

end

end MathlibPlus.Open.NewResearch2.RationalHankel15108
