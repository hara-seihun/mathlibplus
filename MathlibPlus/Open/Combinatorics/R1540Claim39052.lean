import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.Combinatorics.R1540

noncomputable section

abbrev F2Poly := Polynomial (ZMod 2)

private def armF (L : ℕ) : F2Poly :=
  ∑ k ∈ Finset.Icc 1 L,
    Polynomial.C ((L - k + 1 : ℕ) : ZMod 2) *
      (Polynomial.X : F2Poly) ^ k

private def armJ (L : ℕ) : F2Poly :=
  ∑ k ∈ Finset.range (L + 1),
    (Polynomial.X : F2Poly) ^ k

private def connectedArmPolynomial (a b c : ℕ) : F2Poly :=
  armF a + armF b + armF c +
    Polynomial.X * armJ a * armJ b * armJ c

private def foldedPair (w L : ℕ) : F2Poly :=
  (Polynomial.X : F2Poly) ^ (L + 3) +
    Polynomial.X ^ (w - L + 3)

private def foldedArmPolynomial (w a b c : ℕ) : F2Poly :=
  foldedPair w a + foldedPair w b + foldedPair w c

/-- Claim 39052: the fixed-weight characteristic-two transform, the
injectivity of its multiplier, and the resulting equality criterion. -/
def foldedArmTransform_claim39052 : Prop :=
  (∀ (w a b c : ℕ),
    a + b + c = w →
      (1 + (Polynomial.X : F2Poly)) ^ 3 *
          connectedArmPolynomial a b c =
        (Polynomial.C ((w % 2 : ℕ) : ZMod 2) + 1) * Polynomial.X +
          Polynomial.X ^ 2 +
          (Polynomial.C ((w % 2 : ℕ) : ZMod 2) + 1) *
            Polynomial.X ^ 3 +
          Polynomial.X ^ (w + 4) +
          foldedArmPolynomial w a b c) ∧
  Function.Injective (fun p : F2Poly =>
    (1 + (Polynomial.X : F2Poly)) ^ 3 * p) ∧
  (∀ (w a b c a' b' c' : ℕ),
    a + b + c = w → a' + b' + c' = w →
      (connectedArmPolynomial a b c = connectedArmPolynomial a' b' c') ↔
        (foldedArmPolynomial w a b c =
          foldedArmPolynomial w a' b' c'))

end

end MathlibPlus.Open.Combinatorics.R1540
