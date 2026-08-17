import MathlibPlus.Open.Analysis.PrimeScoreBatch

namespace MathlibPlus.Open.Analysis

noncomputable section

/-- The coefficient and strict bound carrier for Claim 1206. -/
def coefficient1149_claim1206 : ℝ :=
  (1149 : ℝ) / 1000

def strictBoundFrom_claim1206 (c : ℝ) (N : ℕ) : Prop :=
  ∀ x : ℝ, (N : ℝ) ≤ x →
    (primeCountingReal x : ℝ) < x / D c x

def leastIntegerStart_claim1206 (c : ℝ) (N : ℕ) : Prop :=
  strictBoundFrom_claim1206 c N ∧
    ∀ M : ℕ, M < N → ¬ strictBoundFrom_claim1206 c M

/--
Claim 1206: coefficient `1.149` has least strict integer start
`42,575,222,505`; the preceding start fails, and the two endpoint margin
prints are retained as decimal-prefix intervals.
-/
def correctedLeastStartCoefficient1149_claim1206 : Prop :=
  let c : ℝ := coefficient1149_claim1206
  let N : ℕ := 42575222505
  let predecessorMargin : ℝ := B ((N - 1 : ℕ) : ℝ) - c
  let endpointMargin : ℝ := c - B (N : ℝ)
  leastIntegerStart_claim1206 c N ∧
    ¬ strictBoundFrom_claim1206 c (N - 1) ∧
    0 < predecessorMargin ∧
      (12680978 : ℝ) / 10 ^ 15 ≤ predecessorMargin ∧
      predecessorMargin < (12680979 : ℝ) / 10 ^ 15 ∧
    0 < endpointMargin ∧
      (21051009 : ℝ) / 10 ^ 17 ≤ endpointMargin ∧
      endpointMargin < (21051010 : ℝ) / 10 ^ 17

end

end MathlibPlus.Open.Analysis
