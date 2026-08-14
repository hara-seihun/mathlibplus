import Mathlib

namespace MathlibPlus
namespace Open
namespace InformationTheory

noncomputable section

open Real

/-- Binary entropy with the endpoint convention supplied by Lean's logarithm. -/
noncomputable def binaryEntropy (x : ℝ) : ℝ :=
  -x * Real.log x - (1 - x) * Real.log (1 - x)

def boppanaEntropyInequality : Prop :=
  ∀ x : ℝ, 0 ≤ x → x ≤ 1 →
    binaryEntropy (x ^ 2) ≥ ((1 + Real.sqrt 5) / 2) * x * binaryEntropy x

end
end InformationTheory
end Open
end MathlibPlus
