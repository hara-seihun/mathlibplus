import MathlibPlus.Open.ResearchFormalization.Claim16737LogConcavity

namespace MathlibPlus.Open.ResearchFormalization

/-- The first explicit finite nonnegative unimodal sequence used in the
counterexample to closure under convolution. -/
def counterexampleSequenceA16736 (n : ℕ) : ℝ :=
  if n = 0 then 1 else if n = 1 then 1 else if n = 2 then 2 else 0

/-- The second explicit finite nonnegative unimodal sequence used in the
counterexample to closure under convolution. -/
def counterexampleSequenceB16736 (n : ℕ) : ℝ :=
  if n = 0 then 1 else if n = 1 then 1 else if n = 2 then 3 else 0

/-- Claim 16736: independence coefficients of a disjoint union are the
coefficient convolution of the component sequences, while arbitrary
nonnegative unimodal sequences need not remain unimodal under convolution.
The universal disjoint-union identity applies in particular to forest
components. -/
def claim16736 : Prop :=
  (∀ {V W : Type*} [Fintype V] [Fintype W]
      (G : SimpleGraph V) (H : SimpleGraph W) (n : ℕ),
    independenceSequence16737 (disjointUnionGraph16737 G H) n =
      convolution16737 (independenceSequence16737 G)
        (independenceSequence16737 H) n) ∧
  finiteSupport16737 counterexampleSequenceA16736 ∧
  finiteSupport16737 counterexampleSequenceB16736 ∧
  nonnegativeSequence16737 counterexampleSequenceA16736 ∧
  nonnegativeSequence16737 counterexampleSequenceB16736 ∧
  unimodalSequence16737 counterexampleSequenceA16736 ∧
  unimodalSequence16737 counterexampleSequenceB16736 ∧
  ¬unimodalSequence16737
    (convolution16737 counterexampleSequenceA16736
      counterexampleSequenceB16736)

end MathlibPlus.Open.ResearchFormalization
