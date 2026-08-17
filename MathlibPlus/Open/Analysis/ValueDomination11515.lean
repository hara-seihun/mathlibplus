import Mathlib
import MathlibPlus.Open.Analysis.DerivativePersistence11516
import MathlibPlus.Open.ResearchFormalization.Batch019ffedc

open Asymptotics Filter
open scoped BigOperators Topology

namespace MathlibPlus.Open.Analysis.ValueDomination11515

noncomputable section

/-- The normalized adverse odd-packet function from the value threshold. -/
def valueOddPacket (M : ℕ) (q : ℝ) : ℝ :=
  (((1 - q) ^ M)⁻¹ - ((1 + q) ^ M)⁻¹) / 2

/-- The logarithmic splice attached to a positive value-threshold root. -/
def valueSplice (q : ℝ) : ℝ :=
  -(1 / 2 : ℝ) * Real.log q

/-- The asymptotic threshold scale after substituting the Hankel exponent. -/
def hankelValueThresholdScale (p : ℝ) (m : ℕ) : ℝ :=
  (1 / 2 : ℝ) * Real.log
      (MathlibPlus.Open.ResearchFormalization.sechHankelExponent p m) -
    (1 / 2 : ℝ) * Real.log (Real.arsinh 1)

/-- Claim 11515: the unique positive odd-packet root has the stated scaled
limit and logarithmic splice, and the all-order sech exponent gives the
fixed-parameter logarithmic order scale. -/
def claim11515_logarithmicValueDominationThreshold : Prop :=
  ∃ qValue : ℕ → ℝ,
    (∀ M : ℕ, 0 < M →
      0 < qValue M ∧
        qValue M < 1 ∧
        valueOddPacket M (qValue M) = 1 ∧
        (∀ q : ℝ, 0 < q → q < 1 →
          valueOddPacket M q = 1 → q = qValue M)) ∧
      Filter.Tendsto
        (fun M : ℕ => (M : ℝ) * qValue M)
        Filter.atTop (nhds (Real.arsinh 1)) ∧
      Filter.Tendsto
        (fun M : ℕ =>
          valueSplice (qValue M) -
            ((1 / 2 : ℝ) * Real.log (M : ℝ) -
              (1 / 2 : ℝ) * Real.log (Real.arsinh 1)))
        Filter.atTop (nhds 0) ∧
      (∀ p : ℝ, 0 < p →
        (∀ m : ℕ,
          MathlibPlus.Open.ResearchFormalization.sechHankelExponent p m =
            (m : ℝ) * (p + (m : ℝ) - 1)) ∧
        IsTheta atTop
          (fun m : ℕ =>
            MathlibPlus.Open.ResearchFormalization.sechHankelExponent p m)
          (fun m : ℕ => (m : ℝ) ^ 2) ∧
        IsBigO atTop
          (fun m : ℕ =>
            hankelValueThresholdScale p m - Real.log (m : ℝ))
          (fun _ : ℕ => (1 : ℝ)))

end

end MathlibPlus.Open.Analysis.ValueDomination11515
