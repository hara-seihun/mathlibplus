import MathlibPlus.Open.Analysis.KTypeSelector
import MathlibPlus.Open.Analysis.KTypeSelectorSharp

namespace MathlibPlus.Analysis.KTypeSelector

/-- The sharp asymptotic selector supplies the pointwise least selector. -/
theorem sharpSubsequentialAsymptotics_implies_finiteSelector :
    MathlibPlus.Open.Analysis.KTypeSelector.sharpSubsequentialAsymptotics →
      MathlibPlus.Open.Analysis.KTypeSelector.finiteSelector := by
  intro h
  dsimp [MathlibPlus.Open.Analysis.KTypeSelector.sharpSubsequentialAsymptotics] at h
  dsimp [MathlibPlus.Open.Analysis.KTypeSelector.finiteSelector]
  intro k hk
  rcases h.2 k hk with ⟨mStar, hmStar, _, _⟩
  refine ⟨?_, ?_, ?_⟩
  · intro t
    exact ⟨mStar t, (hmStar t).1, (hmStar t).2⟩
  · norm_num
  · intro n _
    exact Nat.zero_le n

end MathlibPlus.Analysis.KTypeSelector
