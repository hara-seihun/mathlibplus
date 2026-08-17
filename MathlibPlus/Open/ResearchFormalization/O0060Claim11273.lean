import MathlibPlus.Open.Analysis.XiImpedanceHighEnergy

noncomputable section

open Filter Topology
open MathlibPlus.Open

namespace MathlibPlus.Open.ResearchFormalization.O0060Claim11273

/-- The nonzero, non-Cayley-pole domain of the completed phase at fixed x. -/
def phaseRegular (x t : ℝ) : Prop :=
  xi (Complex.ofReal (completedSigma x) +
      Complex.I * Complex.ofReal (completedTau t x)) ≠ 0 ∧
    xi (Complex.ofReal (completedSigma x) -
      Complex.I * Complex.ofReal (completedTau t x)) ≠ 0 ∧
    completedPhase t x ≠ -1

/-- The punctured zero-frequency filter after removing xi zeros and Cayley
poles, for the exact completed phase carrier. -/
def zeroFrequencyFilter (x : ℝ) : Filter ℝ :=
  𝓝[≠] (0 : ℝ) ⊓ Filter.principal {t : ℝ | phaseRegular x t}

/-- Claim 11273: the completed Cayley impedance is real wherever it is
defined, and its logarithm and impedance have the stated zero-frequency
asymptotics on the exact zero/pole-free domain. -/
def claim11273 : Prop :=
  ∀ x : ℝ, (1 / 4 : ℝ) < x →
    (∀ t : ℝ, t ≠ 0 → completedPhase t x ≠ -1 →
      ‖completedPhase t x‖ = 1 ∧
        (cayleyImpedance t x).im = 0) ∧
    (shiftedXi (Complex.ofReal (Real.sqrt x)) ≠ 0 →
      let l := zeroFrequencyFilter x
      Filter.NeBot l ∧
        Asymptotics.IsBigO l
          (fun t : ℝ =>
            Complex.log (completedPhase t x) -
              2 * Complex.I * Complex.ofReal t * zeroFrequencyFunction x)
          (fun t : ℝ => Complex.ofReal (|t| ^ (3 : ℕ))) ∧
        Asymptotics.IsBigO l
          (fun t : ℝ => cayleyImpedance t x - zeroFrequencyFunction x)
          (fun t : ℝ => Complex.ofReal (|t| ^ (2 : ℕ))))

end MathlibPlus.Open.ResearchFormalization.O0060Claim11273
