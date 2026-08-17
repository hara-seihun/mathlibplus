import MathlibPlus.Open.Research.FormalizationBatch_01a004d6

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.R2100.Claim36907

noncomputable section

open MathlibPlus.Open.Research.FormalizationBatch

private def cubeWeight {n : ℕ} (x : Cube n) : ℕ :=
  ∑ i : Fin n, if x i = true then 1 else 0

/-- Claim 36907: in the common-reflection normalization in which all
 directional edge functions are increasing, a cycle's minimum-weight vertex
has two distinct upward cycle neighbors, so both corresponding directional
values are selected. -/
def claim36907 : Prop :=
  ∀ (n : ℕ)
    (f : (i : Fin n) → DirectionDomain n i → Bool),
    increasingNormalization f →
      containsCycle (cubeAdjacency f) →
        ∃ k : ℕ, 3 ≤ k ∧
          ∃ v : Fin k → Cube n,
            Function.Injective v ∧
              (∀ i, cubeAdjacency f (v i) (v (cycleNext i))) ∧
                ∃ t : Fin k, ∃ u : Fin k, ∃ i j : Fin n,
                  i ≠ j ∧
                    cycleNext u = t ∧
                      cubeWeight (v t) ≤ cubeWeight (v u) ∧
                        (∀ w : Fin k, cubeWeight (v t) ≤ cubeWeight (v w)) ∧
                          v (cycleNext t) = Function.update (v t) i true ∧
                            v u = Function.update (v t) j true ∧
                              v t i = false ∧
                                v t j = false ∧
                                  directionValue f i (v t) = true ∧
                                    directionValue f j (v t) = true

end

end MathlibPlus.Open.ResearchFormalization.R2100.Claim36907
