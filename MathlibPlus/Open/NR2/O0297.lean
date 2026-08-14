import Mathlib

namespace MathlibPlus.Open.NR2.O0297

/-- A prescribed negative sector diagonal cannot equal the diagonal of a
positive Gram feature, regardless of the ambient feature-space dimension.  The
sum-of-sectors equation is retained explicitly. -/
def claim14028 : Prop :=
  ∀ (ι V : Type*) [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (detG₂ : ℝ) (Z : ι → V) (E : ι → ℝ) (d₂ : ι),
    E d₂ < 0 →
      ¬ (detG₂ = ∑ d, E d ∧ ∀ d, E d = ‖Z d‖ ^ 2)

end MathlibPlus.Open.NR2.O0297
