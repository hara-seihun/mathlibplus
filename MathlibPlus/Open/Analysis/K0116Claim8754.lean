import MathlibPlus.Open.Analysis.TrailingBlockUpperSpectralEdge8753

open scoped BigOperators

namespace MathlibPlus.Open.Analysis.K0116Claim8754

open MathlibPlus.Open.Analysis

noncomputable section

/-- The lower spectral edge uses the same eigenvalue carrier as the upper
spectral edge, with an infimum in place of the supremum. -/
def lambdaMin8754 {n : ℕ} (H : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  sInf {z : ℝ | ∃ u : Fin n → ℝ, u ≠ 0 ∧ H.mulVec u = z • u}

/-- Claim 8754: the lower spectral edge of the trailing block is controlled by
lower full-spectrum excursions weighted by reversed endpoint kernels. -/
def trailingBlockLowerSpectralEdge_8754 : Prop :=
  ∀ (N d : ℕ) (hN : 0 < N) (hd : 0 < d ∧ d ≤ N)
    (J : Matrix (Fin N) (Fin N) ℝ)
    (x : Fin N → ℝ) (v : Fin N → Fin N → ℝ) (A : ℝ),
    irreducibleRealJacobi J →
      normalizedSpectralData J x v →
        lambdaMin8754 (trailingPrincipalBlock hd.2 J) ≥
          A -
            ∑ i ∈ Finset.univ.filter (fun i => x i < A),
              (A - x i) *
                (reverseKernel hN (v i) (d - 1) /
                  reverseKernel hN (v i) (N - 1))

end

end MathlibPlus.Open.Analysis.K0116Claim8754
