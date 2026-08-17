import MathlibPlus.Open.ResearchFormalizationBatch.Gaussian

namespace MathlibPlus.Open.ResearchFormalization.R2624Claims42883_42884

open scoped BigOperators
open MathlibPlus.Open.ResearchFormalizationBatch.Gaussian

noncomputable section

/-- The squared norm ratio and the normalized one-hole law. -/
def monicOrthogonalNorm {n : ℕ} (x w : Fin n → ℝ) : ℝ :=
  partitionFunction (n := n) n x w /
    partitionFunction (n := n) (n - 1) x w

def uniqueHoleLaw {n : ℕ} (x w : Fin n → ℝ) (j : Fin n) : ℝ :=
  monicOrthogonalNorm x w * dualWeight x w j

def omittedNodeLaw {n : ℕ} (x w : Fin n → ℝ) (j : Fin n) : ℝ :=
  ((∏ i ∈ (Finset.univ : Finset (Fin n)).erase j, w i) *
      (vandermondeOn x ((Finset.univ : Finset (Fin n)).erase j)) ^ 2) /
    partitionFunction (n := n) (n - 1) x w

def oneHoleExpectation {n : ℕ} (x w v : Fin n → ℝ) : ℝ :=
  ∑ j : Fin n, uniqueHoleLaw x w j * (oneHoleObservable x v j) ^ 2

/-- Claim 42883: the dual-weight expression is positive, normalized, and is
    exactly the law of the unique omitted node in the `(n-1)`-particle
    Vandermonde ensemble. -/
def uniqueHoleProbabilityLaw_claim42883 : Prop :=
  ∀ (n : ℕ) (x w : Fin n → ℝ),
    gaussianRuleData n x w →
      (∀ j : Fin n, 0 < uniqueHoleLaw x w j) ∧
      (∑ j : Fin n, uniqueHoleLaw x w j = 1) ∧
      (∀ j : Fin n,
        uniqueHoleLaw x w j = omittedNodeLaw x w j)

/-- Claim 42884: inverse-Hankel energy is the one-hole expectation with the
    exact normalization by the monic degree-`n-1` norm. -/
def inverseHankelOneHoleExpectation_claim42884 : Prop :=
  ∀ (n : ℕ) (x w : Fin n → ℝ),
    gaussianRuleData n x w →
      ∀ v : Fin n → ℝ,
        quadraticForm (momentHankel x w)⁻¹ v =
          (1 / monicOrthogonalNorm x w) *
            oneHoleExpectation x w v

end

end MathlibPlus.Open.ResearchFormalization.R2624Claims42883_42884
