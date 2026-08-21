import MathlibPlus.Open.Combinatorics.R1540.Core

namespace MathlibPlus.Open.Combinatorics.R1540

noncomputable section

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
