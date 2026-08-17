import MathlibPlus.Open.Analysis.FirstLaguerreDivisorChannels

open scoped BigOperators

namespace MathlibPlus.Open.Analysis.CompletedThetaShellDecomposition15055

noncomputable section

open FirstLaguerreDivisorChannels

/-- Claim 15055: the fixed completed-theta shells, their positive-index source
sum, and the packet-normalized completed-xi transform are the same carriers. -/
def claim15055 : Prop :=
  let f : ℕ → ℝ → ℝ := fun n u ↦
    Real.exp (u / 2) *
      Real.exp (-Real.pi * (n : ℝ) ^ 2 * Real.exp (2 * u))
  let phi : ℕ → ℝ → ℝ := fun n u ↦
    iteratedDeriv 2 (f n) u - (1 / 4 : ℝ) * f n u
  (∀ n : ℕ, 1 ≤ n → ∀ u : ℝ,
      thetaPrimitiveShell n u = f n u ∧
        completedThetaShell n u = phi n u) ∧
    (∀ u : ℝ,
      completedThetaSource u =
        ∑' n : {n : ℕ // 1 ≤ n}, phi n.1 u) ∧
      (∀ x : ℝ,
        thetaFourier completedThetaSource x =
          completedXiOnCriticalLine x)

end

end MathlibPlus.Open.Analysis.CompletedThetaShellDecomposition15055
