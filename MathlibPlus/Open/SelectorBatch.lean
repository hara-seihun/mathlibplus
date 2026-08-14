import Mathlib

namespace MathlibPlus.Open.SelectorBatch

noncomputable section

abbrev SelectorPoly (R : Type*) [CommSemiring R] (d : ℕ) := MvPolynomial (Fin d) R

def selectorVariable {R : Type*} [CommSemiring R] (d : ℕ) (j : ℕ) (hj : j < d) : SelectorPoly R d :=
  MvPolynomial.X ⟨j, hj⟩

def firstVariable (d : ℕ) (hd : 0 < d) : Fin d := ⟨0, hd⟩

def selectorDerivation {R : Type*} [CommRing R] (d : ℕ) (t : R) :
    SelectorPoly R d →ₗ[R] SelectorPoly R d :=
  ∑ j : Fin d, (t ^ j.1) • (MvPolynomial.pderiv j).toLinearMap

def sourceApply {R : Type*} [CommRing R] (d : ℕ)
    (D : SelectorPoly R d → SelectorPoly R d)
    (H : Polynomial (SelectorPoly R d)) : Polynomial (SelectorPoly R d) :=
  H.sum (fun n a => Polynomial.monomial n (D a))

def sourceSelector {R : Type*} [CommRing R] (d : ℕ) (t : R)
    (H : Polynomial (SelectorPoly R d)) : Polynomial (SelectorPoly R d) :=
  sourceApply d (selectorDerivation d t) H

def sourceFirstDerivative {R : Type*} [CommRing R] (d : ℕ) (hd : 0 < d)
    (H : Polynomial (SelectorPoly R d)) : Polynomial (SelectorPoly R d) :=
  sourceApply d (fun p => MvPolynomial.pderiv (firstVariable d hd) p) H

def sourceSupported {R : Type*} [CommRing R] (d : ℕ) (H : Polynomial (SelectorPoly R d)) : Prop :=
  ∀ n : ℕ, n ∈ H.support → n < d

def selectorPhi {R : Type*} [CommRing R] (d : ℕ)
    (H : Polynomial (SelectorPoly R d)) : SelectorPoly R d :=
  H.sum (fun n a =>
    if h : 1 ≤ n ∧ n ≤ d then
      selectorVariable d (n - 1) (by omega) * a
    else 0)

def sourceA {R : Type*} [CommRing R] (d : ℕ)
    (H : Polynomial (SelectorPoly R d)) : SelectorPoly R d :=
  selectorPhi d (Polynomial.X * H)

def sourceL {R : Type*} [CommRing R] (d : ℕ) (hd : 0 < d)
    (H : Polynomial (SelectorPoly R d)) : SelectorPoly R d :=
  MvPolynomial.pderiv (firstVariable d hd) (sourceA d H)

def sourceEvaluate {R : Type*} [CommRing R] (d : ℕ) (t : R)
    (H : Polynomial (SelectorPoly R d)) : SelectorPoly R d :=
  Polynomial.eval (MvPolynomial.C t : SelectorPoly R d) H

def iterateSelector {R : Type*} [CommRing R] (d : ℕ) : List R → SelectorPoly R d → SelectorPoly R d
  | [], f => f
  | t :: ts, f => selectorDerivation d t (iterateSelector d ts f)

def iterateSourceSelector {R : Type*} [CommRing R] (d : ℕ) :
    List R → Polynomial (SelectorPoly R d) → Polynomial (SelectorPoly R d)
  | [], H => H
  | t :: ts, H => sourceSelector d t (iterateSourceSelector d ts H)

def independentSelectorCommutatorClaim {R : Type*} [CommRing R] [CharZero R]
    (d : ℕ) (hd : 0 < d) : Prop :=
  ∀ (H : Polynomial (SelectorPoly R d)) (t : R),
    sourceSupported d H →
      selectorDerivation d t (sourceL d hd H) =
        sourceL d hd (sourceSelector d t H) +
          sourceEvaluate d t (sourceFirstDerivative d hd H)

/-- `List.eraseIdx i` is the source with the `i`th selector omitted. -/
def independentSelectorJetClaim {R : Type*} [CommRing R] [CharZero R]
    (d : ℕ) (hd : 0 < d) : Prop :=
  ∀ (ts : List R) (H : Polynomial (SelectorPoly R d)),
    sourceSupported d H →
      iterateSelector d ts (sourceL d hd H) =
        sourceL d hd (iterateSourceSelector d ts H) +
          ∑ i : Fin ts.length,
            sourceEvaluate d (ts.get i)
              (sourceFirstDerivative d hd
                (iterateSourceSelector d (List.eraseIdx ts i.1) H))

def xOneFree {R : Type*} [CommRing R] (d : ℕ) (hd : 0 < d)
    (f : SelectorPoly R d) : Prop :=
  ∀ m : (Fin d →₀ ℕ), m ∈ f.support → m (firstVariable d hd) = 0

def privateMarkerSelectorClaim {R : Type*} [CommRing R] [CharZero R]
    (d : ℕ) (hd : 0 < d) : Prop :=
  (∀ (t : R) (f : SelectorPoly R d),
      MvPolynomial.pderiv (firstVariable d hd) (selectorDerivation d t f) =
        selectorDerivation d t (MvPolynomial.pderiv (firstVariable d hd) f)) ∧
  (∀ (J : Fin d) (f : SelectorPoly R d),
      (firstVariable d hd).1 < J.1 → xOneFree d hd f →
        xOneFree d hd (MvPolynomial.X J * f) ∧
        ∀ ts : List R,
          MvPolynomial.pderiv (firstVariable d hd)
            (iterateSelector d ts (MvPolynomial.X J * f)) = 0)

def namedVariable10 (j : ℕ) (hj : j < 10) : SelectorPoly ℚ 10 :=
  selectorVariable 10 j hj

def fSix : SelectorPoly ℚ 10 :=
  namedVariable10 2 (by omega) * namedVariable10 2 (by omega) -
    namedVariable10 1 (by omega) * namedVariable10 3 (by omega)

def sourceSix : Polynomial (SelectorPoly ℚ 10) :=
  Polynomial.C (namedVariable10 2 (by omega)) * Polynomial.X ^ 2 -
    Polynomial.C (namedVariable10 3 (by omega)) * Polynomial.X

def privateMarkerSix : SelectorPoly ℚ 10 :=
  namedVariable10 9 (by omega) * fSix

/-- The concrete cap witness from Claim 54705. -/
def concretePrivateMarkerClaim : Prop :=
  sourceA 10 sourceSix = fSix ∧
  sourceL 10 (by omega) sourceSix = 0 ∧
  ∀ ts : List ℚ,
    MvPolynomial.pderiv (firstVariable 10 (by omega))
      (iterateSelector 10 ts privateMarkerSix) = 0

def privateMarkerFullClaim : Prop :=
  (∀ (R : Type*) [CommRing R] [CharZero R] (d : ℕ) (hd : 0 < d),
    privateMarkerSelectorClaim (R := R) d hd) ∧
  concretePrivateMarkerClaim

end

end MathlibPlus.Open.SelectorBatch
