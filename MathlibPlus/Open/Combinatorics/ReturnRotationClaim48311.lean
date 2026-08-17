import Mathlib
import MathlibPlus.Open.ResearchFormalizationBatch_01a000fb_0728_79f0_b278_1ba1ecb6c9c7

namespace MathlibPlus.Open.Combinatorics.ReturnRotationBatch

/-- The sign split, large-height endpoint contradiction, and exact small-height
base list for the first-return rotation argument. -/
def claim48311 : Prop :=
  ∀ (k h : ℕ) (ε : Fin h → ℤ) (S : Fin (h + 1) → ℤ),
    MathlibPlus.Open.ResearchFormalizationBatch_01a000fb_0728_79f0_b278_1ba1ecb6c9c7.firstCentralReturn
      k h ε S →
    ∀ s : Fin h, 0 < s.val →
      let A :=
        MathlibPlus.Open.ResearchFormalizationBatch_01a000fb_0728_79f0_b278_1ba1ecb6c9c7.cutState S s
      let U :=
        MathlibPlus.Open.ResearchFormalizationBatch_01a000fb_0728_79f0_b278_1ba1ecb6c9c7.cutU ε s
      let V :=
        MathlibPlus.Open.ResearchFormalizationBatch_01a000fb_0728_79f0_b278_1ba1ecb6c9c7.cutV ε s
      let C :=
        MathlibPlus.Open.ResearchFormalizationBatch_01a000fb_0728_79f0_b278_1ba1ecb6c9c7.cutC ε s
      let Q :=
        MathlibPlus.Open.ResearchFormalizationBatch_01a000fb_0728_79f0_b278_1ba1ecb6c9c7.cutQ ε s
      let M :=
        MathlibPlus.Open.ResearchFormalizationBatch_01a000fb_0728_79f0_b278_1ba1ecb6c9c7.wordM h
      let t : ℕ := h - s.val
      let K : ℤ := k + h
      let R :=
        MathlibPlus.Open.ResearchFormalizationBatch_01a000fb_0728_79f0_b278_1ba1ecb6c9c7.rotatedResidual ε S s
      let W := -V
      let suffixMinusThenPlus : Prop :=
        ε ⟨s.val, by omega⟩ = -1 ∧
          ∀ j : Fin (h - s.val), 0 < j.val →
            ε ⟨s.val + j.val, by omega⟩ = 1
      (A < 0 →
        Q > 0 ∧
        -M * A > 0 ∧
        (t : ℤ) * Q > 0 ∧
        (h : ℤ) * U > 0 ∧
        R = -M * A + (t : ℤ) * Q + (h : ℤ) * U ∧
        R > 0) ∧
      (A > 0 →
        (R ≥ 0 →
          (((2 : ℤ) ^ t) * A + (t : ℤ) * W) * M ≤
            ((t + h : ℕ) : ℤ) * C + (h : ℤ) * W) ∧
        (h ≥ 8 →
          M > 2 * (h : ℤ) ^ 2 ∧
          (R ≥ 0 →
            W < 3 ∧
            W = 1 ∧
            suffixMinusThenPlus ∧
            K = (2 : ℤ) ^ t * (A + 1) - 2 ∧
            K ≥ (h : ℤ) ∧
            (h : ℤ) ≥ (2 : ℤ) ^ (t + 1) * A + (t : ℤ) ∧
            False))) ∧
      (h ≤ 7 →
        ((h = 2 ∧ k = 0) ∨
          (h = 3 ∧ k = 3) ∨
          (h = 4 ∧ k = 10) ∨
          (h = 5 ∧ k = 5) ∨
          (h = 5 ∧ k = 25) ∨
          (h = 6 ∧ k = 56) ∨
          (h = 7 ∧ k = 19) ∨
          (h = 7 ∧ k = 35) ∨
          (h = 7 ∧ k = 119)) ∧
        ∀ s' : Fin h, 0 < s'.val →
          let A' :=
            MathlibPlus.Open.ResearchFormalizationBatch_01a000fb_0728_79f0_b278_1ba1ecb6c9c7.cutState S s'
          let R' :=
            MathlibPlus.Open.ResearchFormalizationBatch_01a000fb_0728_79f0_b278_1ba1ecb6c9c7.rotatedResidual ε S s'
          A' * R' < 0)

end MathlibPlus.Open.Combinatorics.ReturnRotationBatch
