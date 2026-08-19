import MathlibPlus.Open.Research.BatchO0296

namespace MathlibPlus.Open.ResearchFormalization.Claim14017

open MathlibPlus.Open.Research.BatchO0296
open scoped BigOperators

noncomputable section

/-- The primitive-tuple Möbius selector and the simultaneous diagonal prime
face, on the explicit finite-dimensional age-function carrier. -/
def primitiveTupleMobiusAndDiagonalFace_claim14017 : Prop :=
  ∀ (j : ℕ),
    0 < j →
    ∀ (n : Fin j → ℕ),
      (∀ i : Fin j, 0 < n i) →
      commonDivisorIndicator n =
        ∑ q ∈ (Finset.gcd (Finset.univ : Finset (Fin j)) n).divisors,
          (ArithmeticFunction.moebius q : ℤ) ∧
      ∀ (p : ℕ), Nat.Prime p →
        ∀ (f : (Fin j → ℝ) → ℝ) (x : Fin j → ℝ),
          primeFace p j f x =
            f x - Real.rpow (p : ℝ) (-((j : ℝ) / 2)) *
              f (fun i => x i + Real.log p)

end

end MathlibPlus.Open.ResearchFormalization.Claim14017
