import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.QWronskians

noncomputable section

abbrev CoefficientPolynomial := Polynomial ℚ
abbrev CoefficientSeries := PowerSeries CoefficientPolynomial

def Q : Nat → CoefficientPolynomial
  | 0 => 2 * Polynomial.X - Polynomial.C 3
  | n + 1 =>
      (Polynomial.C (5 / 2) - 2 * Polynomial.X) * Q n +
        2 * Polynomial.X * Polynomial.derivative (Q n)

def formalExpZero (f : CoefficientSeries) : CoefficientSeries :=
  PowerSeries.mk (fun n =>
    ∑ k ∈ Finset.range (n + 1),
      ((k.factorial : ℚ)⁻¹) • (PowerSeries.coeff n (f ^ k)))

def egfQ : CoefficientSeries :=
  PowerSeries.mk (fun n => ((n.factorial : ℚ)⁻¹) • Q n)

def ySeries : CoefficientSeries := PowerSeries.C Polynomial.X
def vSeries : CoefficientSeries := PowerSeries.X

def egfQRight : CoefficientSeries :=
  formalExpZero
      (PowerSeries.C (Polynomial.C (5 / 2 : ℚ)) * vSeries -
        ySeries * (formalExpZero (2 * vSeries) - 1)) *
    (2 * ySeries * formalExpZero (2 * vSeries) - 3)

def iterDerivative : Nat → CoefficientPolynomial → CoefficientPolynomial
  | 0, p => p
  | n + 1, p => Polynomial.derivative (iterDerivative n p)

def wronskian (r : Nat) (f : Fin r → CoefficientPolynomial) : CoefficientPolynomial :=
  (Matrix.of (fun (i : Fin r) (j : Fin r) => iterDerivative i.1 (f j))).det

def W (r : Nat) : CoefficientPolynomial :=
  (Matrix.of (fun (i : Fin r) (j : Fin r) => Q (2 * i.1 + j.1))).det

def evenRows (r : Nat) : Fin r → CoefficientPolynomial :=
  fun i => Q (2 * i.1)

def claim46116 : Prop :=
  Q 0 = 2 * Polynomial.X - Polynomial.C 3 ∧
    (∀ n,
      Q (n + 1) =
        (Polynomial.C (5 / 2 : ℚ) - 2 * Polynomial.X) * Q n +
          2 * Polynomial.X * Polynomial.derivative (Q n)) ∧
    egfQ = egfQRight ∧
    ∀ r, W r =
      (2 * Polynomial.X) ^ (Nat.choose r 2) * wronskian r (evenRows r)

end

end MathlibPlus.Open.QWronskians
