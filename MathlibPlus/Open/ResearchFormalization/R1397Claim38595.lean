import MathlibPlus.Open.ResearchFormalization.R1397PureSection

namespace MathlibPlus.Open.ResearchFormalization.R1397Claim38595

open MathlibPlus.Open.ResearchFormalization.R1397NormalizedShifts
open MathlibPlus.Open.ResearchFormalization.R1397PureSection

noncomputable section

/-- The mandatory central voltage line. -/
def constantCentralLine38595 : Submodule F3 NormalizedShift :=
  Submodule.span F3 ({fun _ : ShiftBase => (1 : F3)} : Set NormalizedShift)

/-- The degree-at-most-two normalized scalar sections in the fixed
`F₃²` carrier. -/
def degreeAtMostTwo38595 (s : NormalizedShift) : Prop :=
  ∃ a b c d e : F3, ∀ i j : F3,
    s (i, j) = a * i + b * j + c * i ^ 2 + d * i * j + e * j ^ 2

/-- The affine-linear rows among the displayed degree-at-most-two sections. -/
def affineLinear38595 (s : NormalizedShift) : Prop :=
  ∃ a b : F3, ∀ i j : F3,
    s (i, j) = a * i + b * j

def nonlinearQuadratic38595 (s : NormalizedShift) : Prop :=
  degreeAtMostTwo38595 s ∧ ¬ affineLinear38595 s

/-- Claim 38595: the 243 degree-at-most-two rows have the mandatory
one-dimensional actual block kernel; nine are affine-linear pure sections,
while the remaining 234 nonlinear quadratic rows have no pure section.  The
central line is contained in every actual relation module, so dimension one is
the minimum possible genuine voltage-module dimension. -/
def claim38595 : Prop :=
  Nat.card {s : NormalizedShift //
      normalized s ∧ degreeAtMostTwo38595 s} = 243 ∧
    Nat.card {s : NormalizedShift //
      normalized s ∧ degreeAtMostTwo38595 s ∧ affineLinear38595 s} = 9 ∧
    Nat.card {s : NormalizedShift //
      normalized s ∧ nonlinearQuadratic38595 s} = 234 ∧
    (∀ s : NormalizedShift,
      normalized s → degreeAtMostTwo38595 s →
        relationModule s = constantCentralLine38595 ∧
          Module.finrank F3 (relationModule s) = 1 ∧
          (affineLinear38595 s ↔ literalPureQuotientSection s) ∧
          (nonlinearQuadratic38595 s →
            ¬ literalPureQuotientSection s)) ∧
    (Module.finrank F3 constantCentralLine38595 = 1) ∧
    (∀ s : NormalizedShift,
      constantCentralLine38595 ≤ relationModule s ∧
        1 ≤ Module.finrank F3 (relationModule s))

end

end MathlibPlus.Open.ResearchFormalization.R1397Claim38595
