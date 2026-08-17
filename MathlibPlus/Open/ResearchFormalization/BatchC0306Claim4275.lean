import Mathlib
import MathlibPlus.Open.Research.FormalizationBatch0306

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.C0306Claim4275

open MathlibPlus.Open.Research

noncomputable def unshiftedGraphKernel (x t s : ℝ) : ℝ :=
  ∑' n : ℕ,
    poissonWeight x n * laguerreAtom n t * laguerreAtom n s

noncomputable def onceShiftedGraphKernel (x t s : ℝ) : ℝ :=
  ∑' n : ℕ,
    poissonWeight x n * ((n : ℝ) / x) * laguerreAtom n t * laguerreAtom n s

noncomputable def firstShiftGraphKernel (x t s : ℝ) : ℝ :=
  ∑' n : ℕ,
    poissonWeight x n * (1 + (n : ℝ) / x) *
      laguerreAtom n t * laguerreAtom n s

/-- Claim 4275: the first-shift Laguerre graph kernel has the exact displayed
coefficient series and is the sum of its unshifted and once-shifted Gram
components.  The only parameter restriction in the source is `x > 0`; `t` and
`s` are unrestricted real arguments. -/
def claim4275 : Prop :=
  ∀ (x : ℝ), 0 < x → ∀ t s : ℝ,
    firstShiftGraphKernel x t s =
        ∑' n : ℕ,
          poissonWeight x n * (1 + (n : ℝ) / x) *
            laguerreAtom n t * laguerreAtom n s ∧
      firstShiftGraphKernel x t s =
        unshiftedGraphKernel x t s + onceShiftedGraphKernel x t s

end MathlibPlus.Open.ResearchFormalization.C0306Claim4275
