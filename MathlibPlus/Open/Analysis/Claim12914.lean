import MathlibPlus.Open.Analysis.ZeroHeightShiftClassification

namespace MathlibPlus.Open.Analysis.Claim12914

/-- Claim 12914: a countable family of integer-shifted carriers is
RH-equivalent, and RH makes every sufficiently large shift admissible. -/
def claim12914 : Prop :=
  (RiemannHypothesis ↔
    ∃ m : ℕ, 1 ≤ m ∧ globalCarrierNonnegative m) ∧
  (RiemannHypothesis →
    ∃ M : ℕ, 1 ≤ M ∧
      ∀ m : ℕ, M ≤ m → globalCarrierNonnegative m)

end MathlibPlus.Open.Analysis.Claim12914
