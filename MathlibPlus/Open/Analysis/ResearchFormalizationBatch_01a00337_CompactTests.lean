import Mathlib

namespace MathlibPlus.Open.Analysis

/-- Anchored unit-Lipschitz tests on a compact interval, including their sup-norm bound. -/
def anchoredUnitLipschitzTests (a b : ℝ) (hab : a ≤ b) : Prop :=
  let I := Set.Icc a b
  letI : CompactSpace I :=
    isCompact_iff_compactSpace.mp (isCompact_Icc (a := a) (b := b))
  let anchor : I := ⟨a, ⟨le_rfl, hab⟩⟩
  let family : Set C(I, ℝ) :=
    {φ | LipschitzWith 1 φ ∧ φ anchor = 0}
  IsCompact family ∧ ∀ φ ∈ family, ‖φ‖ ≤ b - a

end MathlibPlus.Open.Analysis
