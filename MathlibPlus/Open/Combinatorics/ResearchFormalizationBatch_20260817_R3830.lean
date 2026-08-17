import MathlibPlus.Open.Combinatorics.Claim48158

namespace MathlibPlus.Open.Combinatorics.ResearchFormalizationBatch_20260817_R3830

open BigOperators
open scoped BigOperators

/-- The two-long-arm spider used in the centre-decomposition packet. -/
def twoLongArmSpider (r : ℕ) : SimpleGraph (Fin (r + 7)) :=
  SimpleGraph.fromRel (fun v w =>
    (v.val = 0 ∧ 1 ≤ w.val ∧ w.val ≤ r) ∨
    (v.val = 0 ∧ w.val = r + 1) ∨
    (v.val = r + 1 ∧ w.val = r + 2) ∨
    (v.val = r + 2 ∧ w.val = r + 3) ∨
    (v.val = 0 ∧ w.val = r + 4) ∨
    (v.val = r + 4 ∧ w.val = r + 5) ∨
    (v.val = r + 5 ∧ w.val = r + 6))

/-- The actual independence polynomial of the explicit spider. -/
noncomputable def twoLongArmIndependencePolynomial (r : ℕ) : Polynomial ℤ := by
  classical
  exact ∑ S : Finset (Fin (r + 7)),
    if (twoLongArmSpider r).IsIndepSet (S : Set (Fin (r + 7))) then
      Polynomial.X ^ S.card
    else 0

/-- The centre-free and centre-selected polynomial contributions. -/
noncomputable def centreFreeContribution (r : ℕ) : Polynomial ℤ :=
  (1 + Polynomial.X) ^ r *
    (1 + 3 * Polynomial.X + Polynomial.X ^ 2) ^ 2

noncomputable def centreSelectedContribution : Polynomial ℤ :=
  Polynomial.X * (1 + 2 * Polynomial.X) ^ 2

/-- The coefficient-sequence meaning of log-concavity and no internal zeros. -/
def logConcaveNoInternalZeros (p : Polynomial ℤ) : Prop :=
  (∀ n : ℕ, 0 < n →
      p.coeff n ^ 2 ≥ p.coeff (n - 1) * p.coeff (n + 1)) ∧
    (∀ i j k : ℕ, i ≤ j → j ≤ k →
      p.coeff i ≠ 0 → p.coeff k ≠ 0 → p.coeff j ≠ 0)

/-- Statement R-3830.1 on the same explicit carrier, retained as the
centre-decomposition context for Statement R-3830.2. -/
def centreDecomposition_claim48158 : Prop :=
  ∀ r : ℕ,
    twoLongArmIndependencePolynomial r =
      centreFreeContribution r + centreSelectedContribution

/-- Claim 48159: every member of the two-long-arm spider family has a
log-concave independence coefficient sequence with no internal zeros. -/
def logConcavityAndNoInternalZeros_claim48159 : Prop :=
  ∀ r : ℕ,
    twoLongArmIndependencePolynomial r =
        centreFreeContribution r + centreSelectedContribution ∧
      logConcaveNoInternalZeros (twoLongArmIndependencePolynomial r)

end MathlibPlus.Open.Combinatorics.ResearchFormalizationBatch_20260817_R3830
