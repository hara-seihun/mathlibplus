import Mathlib

namespace MathlibPlus.Open.AdmittedBatch

/-- The exact common-index binomial-gcd reduction from Claim 46883. -/
def commonIndexBinomialGcdReduction : Prop :=
  ∀ n k : ℕ, 2 ≤ k ∧ k ≤ n / 2 →
    let d := Nat.gcd n k
    let N := n / d
    let K := k / d
    let B := Nat.choose (n - 1) (k - 1) / K
    let H := n / Nat.gcd n (Nat.choose n k)
    n = d * N ∧
      k = d * K ∧
      K ∣ Nat.choose (n - 1) (k - 1) ∧
      Nat.gcd n (Nat.choose n k) = N * Nat.gcd d B ∧
      H = d / Nat.gcd d B ∧
      H ∣ d ∧ d ∣ k

/-- The exact finite counterexample in Claim 46886. -/
def binaryPrimeSupportPackingBoundFalse : Prop :=
  (∀ k : ℕ, 2 ≤ k → k ≤ 1155 →
    2310 / Nat.gcd 2310 (Nat.choose 2310 k) ≤ 15) ∧
    (∃ k : ℕ, 2 ≤ k ∧ k ≤ 1155 ∧
      2310 / Nat.gcd 2310 (Nat.choose 2310 k) = 15) ∧
    15 < 16 ∧
    16 = 2 ^ ((Nat.primeFactors 2310).card - 1)

/-- Positive-semidefinite order for self-adjoint operators, written by its
quadratic-form comparison. -/
private def psdOperatorLE {𝕜 H : Type*} [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
    (A B : H →L[𝕜] H) : Prop :=
  ∀ x : H,
    RCLike.re (inner 𝕜 x (A x)) ≤ RCLike.re (inner 𝕜 x (B x))

/-- The Douglas contraction criterion from Claim 18016. -/
def douglasContractionCriterion : Prop :=
  ∀ {𝕜 : Type*} [RCLike 𝕜]
    {H₁ H₂ H₃ : Type*}
    [NormedAddCommGroup H₁] [NormedAddCommGroup H₂] [NormedAddCommGroup H₃]
    [InnerProductSpace 𝕜 H₁] [InnerProductSpace 𝕜 H₂] [InnerProductSpace 𝕜 H₃]
    [CompleteSpace H₁] [CompleteSpace H₂] [CompleteSpace H₃],
    ∀ (E : H₁ →L[𝕜] H₂) (O : H₃ →L[𝕜] H₂),
      (∃ C : H₃ →L[𝕜] H₁, O = E.comp C ∧ ‖C‖ ≤ 1) ↔
        psdOperatorLE (O.comp (ContinuousLinearMap.adjoint O))
          (E.comp (ContinuousLinearMap.adjoint E))

end MathlibPlus.Open.AdmittedBatch
