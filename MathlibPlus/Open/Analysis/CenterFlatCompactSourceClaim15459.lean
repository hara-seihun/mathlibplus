import Mathlib

namespace MathlibPlus.Open.Analysis.CenterFlatCompactSourceClaim15459

noncomputable section

open MeasureTheory

/-- The center-flat compact source class `V(a,R)`.  Nontriviality is not
part of the class; claims that require a nonzero source state it separately. -/
def centerFlatSourceClass (a R : ℝ) : Set (ℝ → ℝ) :=
  {q |
    ContDiff ℝ ⊤ q ∧
      Even q ∧
        HasCompactSupport q ∧
          Function.support q ⊆
            Set.Icc (-R) (-a) ∪ Set.Icc a R ∧
            ∫ x : ℝ, q x ∂volume = 0}

/-- Vanishing on the central open interval is the zero-germ condition. -/
def zeroGermAtCenter (a : ℝ) (q : ℝ → ℝ) : Prop :=
  ∀ x : ℝ, x ∈ Set.Ioo (-a) a → q x = 0

/-- Claim 15459: for `0<a<R`, every source in `V(a,R)` is smooth, real-even,
compactly supported in the two displayed outer intervals, has zero integral,
and has the zero germ at the center. -/
def claim15459_centerFlatCompactSourceClass : Prop :=
  ∀ (a R : ℝ),
    0 < a →
      a < R →
        ∀ q : ℝ → ℝ,
          q ∈ centerFlatSourceClass a R →
            ContDiff ℝ ⊤ q ∧
              Even q ∧
                HasCompactSupport q ∧
                  Function.support q ⊆
                    Set.Icc (-R) (-a) ∪ Set.Icc a R ∧
                    ∫ x : ℝ, q x ∂volume = 0 ∧
                    zeroGermAtCenter a q

end

end MathlibPlus.Open.Analysis.CenterFlatCompactSourceClaim15459
