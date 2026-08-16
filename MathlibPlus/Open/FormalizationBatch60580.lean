import Mathlib

noncomputable section

namespace MathlibPlus.Open.FormalizationBatch60580

abbrev SparsePolynomial := Polynomial (Polynomial (Polynomial ℤ))

def zVar : SparsePolynomial := Polynomial.C (Polynomial.C Polynomial.X)
def xVar : SparsePolynomial := Polynomial.X
def yVar : SparsePolynomial := Polynomial.C Polynomial.X

def f₁ (d : ℤ) : SparsePolynomial :=
  xVar - yVar * zVar ^ Int.toNat (d - 2)

def f₂ (_d : ℤ) : SparsePolynomial := xVar

def f₁' (d : ℤ) : SparsePolynomial :=
  xVar - yVar * zVar ^ Int.toNat (d - 2)

def f₂' (_d : ℤ) : SparsePolynomial := xVar - 1

def xFree (p : SparsePolynomial) : Prop :=
  ∀ n : ℕ, n ≠ 0 → p.coeff n = 0

def claim60580 : Prop :=
  ∀ d : ℤ, 3 ≤ d →
    Polynomial.Monic (f₁ d) ∧
    Polynomial.Monic (f₂ d) ∧
    Polynomial.Monic (f₁' d) ∧
    Polynomial.Monic (f₂' d) ∧
    xFree (f₁ d - xVar) ∧
    xFree (f₂ d - xVar) ∧
    xFree (f₁' d - xVar) ∧
    xFree (f₂' d - xVar) ∧
    ((f₁ d - xVar) + (f₂ d - xVar) -
        ((f₁' d - xVar) + (f₂' d - xVar)) = 1) ∧
    ((f₁ d - xVar) * (f₂ d - xVar) -
        (f₁' d - xVar) * (f₂' d - xVar) =
      -yVar * zVar ^ Int.toNat (d - 2))

abbrev TraceCoefficientRing := MvPolynomial ℕ ℤ
abbrev TracePolynomial := Polynomial TraceCoefficientRing

def traceVariable (n : ℕ) : TraceCoefficientRing := MvPolynomial.X n
def traceZ : TracePolynomial := Polynomial.X
def traceX (d : ℤ) : TracePolynomial := Polynomial.C (traceVariable (Int.toNat d))
def traceY : TracePolynomial := Polynomial.C (traceVariable 2)

def traceF₁ (d : ℤ) : TracePolynomial :=
  traceX d - traceY * traceZ ^ Int.toNat (d - 2)

def traceF₂ (d : ℤ) : TracePolynomial := traceX d
def traceF₁' (d : ℤ) : TracePolynomial :=
  traceX d - traceY * traceZ ^ Int.toNat (d - 2)
def traceF₂' (d : ℤ) : TracePolynomial := traceX d - 1

def rootForgettingTrace (p : TracePolynomial) : TraceCoefficientRing :=
  p.support.sum (fun a => traceVariable (a + 1) * p.coeff a)

def traceProductDefect (d : ℤ) : TracePolynomial :=
  traceF₁ d * traceF₂ d - traceF₁' d * traceF₂' d

def traceScalarIdentity (d : ℤ) : TraceCoefficientRing :=
  traceVariable 2 * traceVariable (Int.toNat d) -
    traceVariable 2 * traceVariable (Int.toNat d)

def claim60581 : Prop :=
  (∀ (a : ℕ) (P : TraceCoefficientRing),
    rootForgettingTrace (Polynomial.monomial a P) =
      traceVariable (a + 1) * P) ∧
  (∀ d : ℤ, 3 ≤ d →
    traceProductDefect d =
      traceX d - traceY * traceZ ^ Int.toNat (d - 2) ∧
    rootForgettingTrace (traceZ * traceProductDefect d) =
      rootForgettingTrace (traceZ * traceX d) -
        rootForgettingTrace (traceY * traceZ ^ Int.toNat (d - 1)) ∧
    rootForgettingTrace (traceZ * traceProductDefect d) =
      traceScalarIdentity d ∧
    traceScalarIdentity d = 0 ∧
    (∀ D : Derivation ℤ TraceCoefficientRing TraceCoefficientRing,
      D (traceScalarIdentity d) = 0) ∧
    (∀ D : Derivation ℤ TracePolynomial TracePolynomial,
      D (Polynomial.C (traceScalarIdentity d)) = 0) ∧
    Polynomial.derivative (Polynomial.C (traceScalarIdentity d)) = 0)

end MathlibPlus.Open.FormalizationBatch60580
