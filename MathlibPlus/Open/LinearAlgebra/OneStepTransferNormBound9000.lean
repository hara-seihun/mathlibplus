import MathlibPlus.Open.LinearAlgebra.LayerTransferBound

open scoped BigOperators

namespace MathlibPlus.Open.LinearAlgebra

noncomputable section

def oneStepTwoSidedNormBound_9000 : Prop :=
  ∀ (p_N q_N : ℕ) (a_N : ℕ → ℝ) (lam_N c_N : ℝ),
    (hpq : p_N ≤ q_N) →
      0 < c_N →
        (∀ r ∈ Finset.Icc p_N (q_N + 1), 0 < a_N r) →
          let K_N := localConditioning a_N lam_N c_N p_N q_N hpq
          ∀ r ∈ Finset.Icc p_N q_N,
            matrixInfinityNorm (jacobiTransferMatrix a_N lam_N r) ≤
                2 * K_N ^ 2 ∧
              matrixInfinityNorm
                  ((jacobiTransferMatrix a_N lam_N r)⁻¹) ≤
                2 * K_N ^ 2

end

end MathlibPlus.Open.LinearAlgebra
