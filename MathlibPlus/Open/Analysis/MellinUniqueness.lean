import Mathlib.Analysis.MellinTransform

namespace MathlibPlus.Open.Analysis

/-- The exact compact-annular Mellin-source carrier used by Claim 3832.  Its
integrability/convergence conditions are part of the source class rather than
smuggled as extra hypotheses into the uniqueness assertion. -/
def compactAnnularMellinSource (q : ℝ → ℂ) : Prop :=
  ∃ a b : ℝ,
    0 < a ∧ a < b ∧
      Continuous q ∧
      HasCompactSupport q ∧
      tsupport q ⊆ Set.Icc a b ∧
      (∀ s : ℂ, MellinConvergent q s)

/-- Claim 3832: an identically zero Mellin transform has zero source on the
compact positive annular carrier. -/
def compactAnnularMellinUniqueness : Prop :=
  ∀ (q : ℝ → ℂ), compactAnnularMellinSource q →
    mellin q = (fun _ : ℂ => 0) → q = 0

end MathlibPlus.Open.Analysis
