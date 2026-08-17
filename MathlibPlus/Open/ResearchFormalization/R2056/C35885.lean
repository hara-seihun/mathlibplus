import MathlibPlus.Open.ResearchFormalization.R2056.C35886

namespace MathlibPlus.Open.ResearchFormalization.R2056C35885

noncomputable section

open MathlibPlus.Open.ResearchFormalization.R2056C35886

/-- The two-step index relation on either three-point track. -/
def twoStep (i j : Fin 3) : Prop :=
  i.val + 2 = j.val ∨ j.val + 2 = i.val

/-- Both two-step track vectors have the displayed common length. -/
def twoStepLengths (L : ℝ) : Prop :=
  (∀ i j : Fin 3, twoStep i j → euclidLength (U i - U j) = L) ∧
    (∀ i j : Fin 3, twoStep i j → euclidLength (V i - V j) = L)

/-- Every nonzero single-family displacement is either one track step or a
    two-step displacement, with the corresponding exact length. -/
def singleFamilyLengthClassification (L : ℝ) : Prop :=
  (∀ i j : Fin 3, i ≠ j →
    ((euclidLength (U i - U j) = 1 ↔ Nat.dist i.val j.val = 1) ∧
      (euclidLength (U i - U j) = L ↔ Nat.dist i.val j.val = 2))) ∧
    (∀ i j : Fin 3, i ≠ j →
      ((euclidLength (V i - V j) = 1 ↔ Nat.dist i.val j.val = 1) ∧
        (euclidLength (V i - V j) = L ↔ Nat.dist i.val j.val = 2)))

/-- The quantitative mixed-family separation chain, on the actual track
    displacements of the nine-point carrier. -/
def mixedFamilySeparation (L c : ℝ) : Prop :=
  ∀ i i' j j' : Fin 3,
    let A := U i - U i'
    let B := V j - V j'
    A ≠ (0, 0) →
      B ≠ (0, 0) →
        let r := euclidLength A
        let s := euclidLength B
        1 ≤ r ∧
          r ≤ L ∧
            1 ≤ s ∧
              s ≤ L ∧
                absCosine A B ≤ c ∧
                  euclidSq (A + B) ≥ r ^ 2 + s ^ 2 - 2 * c * r * s ∧
                    r ^ 2 + s ^ 2 - 2 * c * r * s ≥ 2 - 2 * c ∧
                      2 - 2 * c = (5 - Real.sqrt 5) / 2 ∧
                        1 < (5 - Real.sqrt 5) / 2

/-- If exactly one family contributes, the remaining nonzero displacement has
    the one-step or two-step length asserted in the construction. -/
def singleFamilyContributionLengths (L : ℝ) : Prop :=
  (∀ i i' j : Fin 3,
    i ≠ i' →
      (euclidLength ((U i - U i') + (V j - V j)) = 1 ∨
        euclidLength ((U i - U i') + (V j - V j)) = L)) ∧
    (∀ i j j' : Fin 3,
      j ≠ j' →
        (euclidLength ((U i - U i) + (V j - V j')) = 1 ∨
          euclidLength ((U i - U i) + (V j - V j')) = L))

/-- The actual unit-distance relation on the nine points is exactly the
    twelve-edge grid relation. -/
def onlyUnitEdges : Prop :=
  ∀ s t s' t' : Fin 3,
    unitPair s t s' t' ↔ gridAdjacent s t s' t'

/-- Claim 35885: the exact two-step lengths, mixed-displacement chain,
    single-family alternatives, and twelve-edge unit-graph conclusion. -/
def claim35885_unitDistanceSeparation : Prop :=
  let L := 2 * Real.cos (Real.pi / 20)
  let c := Real.cos (2 * Real.pi / 5)
  twoStepLengths L ∧
    singleFamilyLengthClassification L ∧
      1 < L ∧
        L < 2 ∧
          c = (Real.sqrt 5 - 1) / 4 ∧
            c < 1 / 2 ∧
              mixedFamilySeparation L c ∧
                singleFamilyContributionLengths L ∧
                  onlyUnitEdges

end

end MathlibPlus.Open.ResearchFormalization.R2056C35885
