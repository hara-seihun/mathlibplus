import Mathlib

noncomputable section
open scoped BigOperators

namespace MathlibPlus.Open.Algebra.Batch60733

abbrev Positive := ℕ+
abbrev R := MvPolynomial (Option Positive) ℤ

def shiftIndex (r : ℕ) (s : Positive) : Positive :=
  ⟨r + (s : ℕ), Nat.add_pos_right r s.pos⟩

def z : R := MvPolynomial.X none

def x (i : Positive) : R := MvPolynomial.X (some i)

def transportedMonomial (s : Positive) (m : (Option Positive) →₀ ℕ) (c : ℤ) : R :=
  MvPolynomial.monomial
    (m.erase none + Finsupp.single (some (shiftIndex (m none) s)) 1) c

def phi (s : Positive) (P : R) : R :=
  ∑ m ∈ P.support, transportedMonomial s m (MvPolynomial.coeff m P)

def xCoefficient (d : Positive) (k : ℕ) (P : R) : R :=
  ∑ m ∈ P.support,
    if m (some d) = k then
      MvPolynomial.monomial (m.erase (some d)) (MvPolynomial.coeff m P)
    else 0

def zCoefficient (n : ℕ) (H : R) : R :=
  ∑ m ∈ H.support,
    if m none = n then
      MvPolynomial.monomial (m.erase none) (MvPolynomial.coeff m H)
    else 0

def delta (d : Positive) (t : Positive) (H : R) : R :=
  if (t : ℕ) ≤ (d : ℕ) then
    zCoefficient ((d : ℕ) - (t : ℕ)) H
  else 0

def previousXCoefficient (d : Positive) (k : ℕ) (P : R) : R :=
  if 0 < k then xCoefficient d (k - 1) P else 0

def hatPhi (d : Positive) (t : Positive) (H : R) : R :=
  phi t H - x d * delta d t H

def B (P Q : R) : R :=
  phi 1 P * phi 1 Q + phi 2 (P * Q)

def aOne (d : Positive) (i : ℕ) (P : R) : R :=
  hatPhi d 1 (xCoefficient d i P) + delta d 1 (previousXCoefficient d i P)

def pqCoefficient (d : Positive) (k : ℕ) (P Q : R) : R :=
  xCoefficient d k (P * Q)

def convolution (d : Positive) (k : ℕ) (P Q : R) : R :=
  ∑ i ∈ Finset.range (k + 1),
    xCoefficient d i P * xCoefficient d (k - i) Q

def cTwo (d : Positive) (k : ℕ) (P Q : R) : R :=
  hatPhi d 2 (pqCoefficient d k P Q) +
    delta d 2 (previousXCoefficient d k (P * Q))

def claim60733 : Prop :=
  ∀ (d : Positive), 2 ≤ d →
    ∀ (P Q : R),
      (∀ (t : Positive) (k : ℕ),
        xCoefficient d k (phi t P) =
          hatPhi d t (xCoefficient d k P) +
            delta d t (previousXCoefficient d k P)) ∧
      (∀ (k : ℕ),
        pqCoefficient d k P Q = convolution d k P Q →
          xCoefficient d k (B P Q) =
            (∑ i ∈ Finset.range (k + 1),
              aOne d i P * aOne d (k - i) Q) + cTwo d k P Q)

end MathlibPlus.Open.Algebra.Batch60733
