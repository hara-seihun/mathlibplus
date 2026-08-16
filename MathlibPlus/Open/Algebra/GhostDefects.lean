import Mathlib

namespace MathlibPlus.Open

noncomputable section

/- The coefficient ring named in the claims is the multivariate polynomial ring
   ℤ[c,d,C,D], with the four variables represented by Fin 4. -/
abbrev GhostBase := MvPolynomial (Fin 4) ℤ

namespace GhostBase

def c : GhostBase := MvPolynomial.X 0
def d : GhostBase := MvPolynomial.X 1
def capC : GhostBase := MvPolynomial.X 2
def capD : GhostBase := MvPolynomial.X 3

end GhostBase

abbrev GhostField := FractionRing GhostBase

def ghostC : GhostField := algebraMap GhostBase GhostField GhostBase.c
def ghostD : GhostField := algebraMap GhostBase GhostField GhostBase.d
def ghostCapC : GhostField := algebraMap GhostBase GhostField GhostBase.capC
def ghostCapD : GhostField := algebraMap GhostBase GhostField GhostBase.capD

def binomialPolynomial {R : Type*} [CommRing R]
    (M : ℕ) (c d : R) : Polynomial R :=
  Polynomial.X ^ M + Polynomial.C c * Polynomial.X + Polynomial.C d

def plusPolynomial (M : ℕ) : Polynomial GhostField :=
  binomialPolynomial M ghostC ghostD

def minusPolynomial (M : ℕ) : Polynomial GhostField :=
  binomialPolynomial M ghostCapC ghostCapD

def rootFactorProduct {R : Type*} [CommRing R]
    (M : ℕ) (r : Fin M → R) : Polynomial R :=
  ∏ i : Fin M, (Polynomial.X - Polynomial.C (r i))

def elementaryCoefficient {R : Type*} [CommRing R]
    (M : ℕ) (r : Fin M → R) (k : ℕ) : R :=
  (∏ i : Fin M, (1 + Polynomial.C (r i) * Polynomial.X)).coeff k

def powerSum {R : Type*} [CommRing R]
    (M : ℕ) (r : Fin M → R) (k : ℕ) : R :=
  ∑ i : Fin M, (r i) ^ k

def commonUniversalSplitting (M : ℕ) (E : Type*) [Field E]
    [Algebra GhostField E] (a b : Fin M → E) : Prop :=
  Polynomial.IsSplittingField GhostField E (plusPolynomial M * minusPolynomial M) ∧
    Polynomial.map (algebraMap GhostField E) (plusPolynomial M) =
      rootFactorProduct M a ∧
    Polynomial.map (algebraMap GhostField E) (minusPolynomial M) =
      rootFactorProduct M b

def universalBaseMap (E : Type*) [Field E] [Algebra GhostField E] :
    GhostBase →+* E :=
  (algebraMap GhostField E).comp (algebraMap GhostBase GhostField)

def elementaryDefectPlus (M : ℕ) : GhostBase :=
  ((-1 : GhostBase) ^ (M - 1)) * (GhostBase.c - GhostBase.capC)

def elementaryDefectMinus (M : ℕ) : GhostBase :=
  ((-1 : GhostBase) ^ M) * (GhostBase.d - GhostBase.capD)

def specializedPlusPolynomial {R : Type*} [CommRing R]
    (M : ℕ) (σ : GhostBase →+* R) : Polynomial R :=
  binomialPolynomial M (σ GhostBase.c) (σ GhostBase.d)

def specializedMinusPolynomial {R : Type*} [CommRing R]
    (M : ℕ) (σ : GhostBase →+* R) : Polynomial R :=
  binomialPolynomial M (σ GhostBase.capC) (σ GhostBase.capD)

/-- Claim 60622: the two sparse polynomial families have the stated
coefficient defects, including their specialization statement. -/
def claim60622 : Prop :=
  (∀ (M : ℕ), 2 ≤ M →
    ∀ (E : Type*) [Field E] [Algebra GhostField E]
      (a b : Fin M → E),
      commonUniversalSplitting M E a b →
        (∀ (k : ℕ), 1 ≤ k → k ≤ M - 2 →
          elementaryCoefficient M a k = 0 ∧
          elementaryCoefficient M b k = 0) ∧
        elementaryCoefficient M a (M - 1) -
            elementaryCoefficient M b (M - 1) =
          universalBaseMap E (elementaryDefectPlus M) ∧
        elementaryCoefficient M a M - elementaryCoefficient M b M =
          universalBaseMap E (elementaryDefectMinus M) ∧
        LinearIndependent ℤ ![elementaryDefectPlus M, elementaryDefectMinus M]) ∧
  (∀ (M : ℕ), 2 ≤ M →
    ∀ (R : Type*) [CommRing R] (σ : GhostBase →+* R)
      (a b : Fin M → R),
      specializedPlusPolynomial M σ = rootFactorProduct M a →
      specializedMinusPolynomial M σ = rootFactorProduct M b →
        (∀ (k : ℕ), 1 ≤ k → k ≤ M - 2 →
          elementaryCoefficient M a k = 0 ∧
          elementaryCoefficient M b k = 0) ∧
        elementaryCoefficient M a (M - 1) -
            elementaryCoefficient M b (M - 1) =
          (-1 : R) ^ (M - 1) * (σ GhostBase.c - σ GhostBase.capC) ∧
        elementaryCoefficient M a M - elementaryCoefficient M b M =
          (-1 : R) ^ M * (σ GhostBase.d - σ GhostBase.capD))

/-- Claim 60623: the power sums have the lower vanishing range, the two
first unseen defects, and the explicit M = 2 boundary formula. -/
def claim60623 : Prop :=
  ∀ (M : ℕ), 2 ≤ M →
    ∀ (E : Type*) [Field E] [Algebra GhostField E]
      (a b : Fin M → E),
      commonUniversalSplitting M E a b →
        (∀ (k : ℕ), 1 ≤ k → k ≤ M - 2 →
          powerSum M a k = 0 ∧ powerSum M b k = 0) ∧
        (3 ≤ M →
          powerSum M a (M - 1) - powerSum M b (M - 1) =
              -((M - 1 : ℕ) : E) *
                (universalBaseMap E GhostBase.c -
                  universalBaseMap E GhostBase.capC) ∧
          powerSum M a M - powerSum M b M =
              -(M : E) *
                (universalBaseMap E GhostBase.d -
                  universalBaseMap E GhostBase.capD)) ∧
        (M = 2 →
          elementaryCoefficient M a 1 - elementaryCoefficient M b 1 =
              -(universalBaseMap E GhostBase.c -
                universalBaseMap E GhostBase.capC) ∧
          elementaryCoefficient M a 2 - elementaryCoefficient M b 2 =
              universalBaseMap E GhostBase.d -
                universalBaseMap E GhostBase.capD ∧
          powerSum M a 1 - powerSum M b 1 =
              -(universalBaseMap E GhostBase.c -
                universalBaseMap E GhostBase.capC) ∧
          powerSum M a 2 - powerSum M b 2 =
              (universalBaseMap E GhostBase.c) ^ 2 -
                (universalBaseMap E GhostBase.capC) ^ 2 -
                (2 : E) *
                  (universalBaseMap E GhostBase.d -
                    universalBaseMap E GhostBase.capD))

end

end MathlibPlus.Open
