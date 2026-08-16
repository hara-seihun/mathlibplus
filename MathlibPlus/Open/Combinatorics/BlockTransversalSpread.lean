import Mathlib

namespace MathlibPlus.Open.Combinatorics

/-- The exact transversal family arising from disjoint blocks is q-spread and
R-spread, with the stated link cardinalities. -/
def blockTransversalSpread : Prop :=
  ∀ (R : ℝ) (q : ℤ) (w : ℕ) (α : Type*)
    [Fintype α] [DecidableEq α],
    1 < R → (q : ℝ) > max R 2 → 1 ≤ w →
      ∀ (blocks : Fin w → Finset α),
        (∀ i, (blocks i).card = q.toNat) →
        (∀ i j, i ≠ j → Disjoint (blocks i) (blocks j)) →
        let isTransversal : Finset α → Prop :=
          fun s => s.card = w ∧ ∀ i, (s ∩ blocks i).card = 1
        let family : Finset (Finset α) :=
          Finset.univ.filter isTransversal
        let link : Finset α → Finset (Finset α) :=
          fun trace => family.filter (fun s => trace ⊆ s)
        let meetingBlocks : Finset α → Finset (Fin w) :=
          fun trace =>
            Finset.univ.filter (fun i => (trace ∩ blocks i).Nonempty)
        let exactQSpread : Prop :=
          ∀ trace,
            (link trace).card ≤ q.toNat ^ (w - trace.card)
        let RSpread : Prop :=
          ∀ trace,
            R ^ trace.card * ((link trace).card : ℝ) ≤ (family.card : ℝ)
        family.card = q.toNat ^ w ∧
          (∀ s ∈ family, s.card = w) ∧
          exactQSpread ∧
          RSpread ∧
          (∀ (trace : Finset α) (t : ℕ),
            (∀ x ∈ trace, ∃ i, x ∈ blocks i) →
            (∀ i, (trace ∩ blocks i).card ≤ 1) →
            (meetingBlocks trace).card = t →
            (link trace).card = q.toNat ^ (w - t)) ∧
          (∀ (trace : Finset α) (i : Fin w),
            2 ≤ (trace ∩ blocks i).card →
            (link trace).card = 0)

end MathlibPlus.Open.Combinatorics
