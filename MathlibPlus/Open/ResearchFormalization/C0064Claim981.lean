import MathlibPlus.Open.Analysis.PrimeCountingRepairs

namespace MathlibPlus.Open.AnalyticNumberTheory.PrimeCounting

noncomputable section

open MathlibPlus.Open.Analysis

/-- Axler's score on the reviewed real prime-counting carrier. -/
def auditScore_claim981 (x : ℝ) : ℝ :=
  Real.log x - x / primeCountingReal x

/-- The strict published-coefficient bound beginning at an integer N. -/
def strictBoundFromInteger_claim981 (r : AuditRow) (N : ℕ) : Prop :=
  ∀ x : ℝ, (N : ℝ) ≤ x →
    primeCountingReal x < x / (Real.log x - r.publishedCoeff)

/-- Claim 981: every published start is the least integer start for its
strict bound, with the stated score margins, predecessor plateau, and
failure at the predecessor. -/
def everyPublishedIntegerStartMinimal_claim981 : Prop :=
  ∀ r ∈ auditRows,
    auditScore_claim981 (r.start : ℝ) < r.publishedCoeff ∧
      r.publishedCoeff < auditScore_claim981 ((r.start - 1 : ℕ) : ℝ) ∧
      Nat.primeCounting (r.start - 1) = Nat.primeCounting r.start ∧
      strictBoundFromInteger_claim981 r r.start ∧
      (∀ N : ℕ, strictBoundFromInteger_claim981 r N → r.start ≤ N) ∧
      ¬ strictBoundFromInteger_claim981 r (r.start - 1) ∧
      ¬ primeCountingReal ((r.start - 1 : ℕ) : ℝ) <
        ((r.start - 1 : ℕ) : ℝ) /
          (Real.log ((r.start - 1 : ℕ) : ℝ) - r.publishedCoeff)

end

end MathlibPlus.Open.AnalyticNumberTheory.PrimeCounting
