import Mathlib

namespace MathlibPlus.Open.Combinatorics

/-- Claim 36882: greedy indexed-trace matching. `T i` is a uniform p-element
trace, and the filtered-universe bound is the source's coordinate-degree
hypothesis. The conclusion records pairwise-disjoint retained indices and the
equivalent natural-number counting inequality; for `p = 0` the denominator is
one, forcing all empty traces to be retainable. -/
def greedyPairwiseDisjointIndexedTraceMatching_claim36882 : Prop :=
  ∀ (ι Y : Type*) [Fintype ι] [DecidableEq ι] [Fintype Y] [DecidableEq Y],
    ∀ (T : ι → Finset Y) (p s : ℕ),
      (∀ i : ι, (T i).card = p) →
      (∀ y : Y,
        (Finset.univ.filter (fun i : ι => y ∈ T i)).card ≤ s) →
      ∃ I : Finset ι,
        (∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (T i) (T j)) ∧
          Fintype.card ι ≤ (1 + p * (s - 1)) * I.card

end MathlibPlus.Open.Combinatorics
