import Mathlib

namespace MathlibPlus.Open.FormalizationBatch

noncomputable section
open scoped BigOperators

private def dividedBracket {R : Type} [CommRing R]
    (w rho : R) (p : Nat) : R :=
  ∑ i : Fin p, w ^ (p - 1 - (i : Nat)) * rho ^ (i : Nat)

private def intervalState {R : Type} [CommRing R]
    (L m p : Nat) (w rho : R) : R :=
  if p = 0 then 0 else
    w ^ m * rho ^ (L - m - p + 1) * dividedBracket w rho p

private def intervalBox {R : Type} [CommRing R]
    (L m p : Nat) (w rho : R) : R :=
  intervalState L m p w rho - intervalState L m (p + 1) w rho -
    intervalState L (m + 1) p w rho + intervalState L (m + 1) (p + 1) w rho

/-- Claim 55867: interval states and endpoint evaluations. -/
def claim_55867 : Prop :=
  ∀ (R : Type) [CommRing R] (L m p : Nat) (w rho : R),
    (intervalState L m 0 w rho = 0) ∧
    (p ≥ 1 → m + p ≤ L + 1 →
      intervalState L m p 0 rho = (if m = 0 then rho ^ L else 0) ∧
      intervalState L m p rho rho = (p : R) * rho ^ L)

/-- Claim 55869: the Boolean square identity and its integral quotient. -/
def claim_55869 : Prop :=
  ∀ (R : Type) [CommRing R] (L m p : Nat) (w rho : R),
    L ≥ 2 → p ≥ 1 → m + p ≤ L - 1 →
    let box := intervalBox L m p w rho
    let h := w * (w - rho)
    (box = w ^ (m + p) * rho ^ (L - m - p - 1) * (w - rho) ∧
      box = h * (w ^ (m + p - 1) * rho ^ (L - m - p - 1)) ∧
      intervalBox L m p 0 rho = 0 ∧
      intervalBox L m p rho rho = 0)

private def homogeneousBinary {R : Type} [CommRing R]
    (L : Nat) (c : Fin (L + 1) → R) : MvPolynomial (Fin 2) R :=
  ∑ i : Fin (L + 1),
    MvPolynomial.C (c i) * MvPolynomial.X 0 ^ (i : Nat) *
      MvPolynomial.X 1 ^ (L - (i : Nat))

private def boxPolynomial {R : Type} [CommRing R]
    (L k : Nat) : MvPolynomial (Fin 2) R :=
  intervalBox L 0 k (MvPolynomial.X 0) (MvPolynomial.X 1)

private def quotientPolynomial {R : Type} [CommRing R]
    (L : Nat) (a : Fin (L - 1) → R) : MvPolynomial (Fin 2) R :=
  ∑ k : Fin (L - 1),
    MvPolynomial.C (a k) * MvPolynomial.X 0 ^ (k : Nat) *
      MvPolynomial.X 1 ^ (L - 2 - (k : Nat))

/-- Claim 55870: canonical contraction of homogeneous endpoint-zero aggregates. -/
def claim_55870 : Prop :=
  ∀ (R : Type) [CommRing R] (L : Nat) (c : Fin (L + 1) → R),
    L ≥ 2 → c 0 = 0 → (∑ i : Fin (L + 1), c i) = 0 →
    ∃! a : Fin (L - 1) → R,
      let G := homogeneousBinary L c
      let h := MvPolynomial.X 0 * (MvPolynomial.X 0 - MvPolynomial.X 1)
      G = ∑ k : Fin (L - 1),
        MvPolynomial.C (a k) * boxPolynomial L ((k : Nat) + 1) ∧
      G = h * quotientPolynomial L a

end
end MathlibPlus.Open.FormalizationBatch
