import MathlibPlus.Open.ResearchFormalization.O0338.PositiveOrderAndDeltaPrime15523_15526

namespace MathlibPlus.Open.ResearchFormalization.O0338

noncomputable section

open Filter Set TopologicalSpace Distribution
open scoped BigOperators Distributions Topology

/-- The point-shift distribution used by the finite-difference specialization. -/
noncomputable def pointShift15517 (t : ℝ) : RealDistribution :=
  deltaDerivative t 0

/-- The signed forward finite difference whose distributional limit is the
`k`-th derivative of a point shift.  The signs match the convention that
`deltaDerivative t k` acts by `(-1)^k` times the `k`-th test-function jet. -/
noncomputable def finiteDifferenceDerivative15517
    (t : ℝ) (k : ℕ) (h : ℝ) : RealDistribution :=
  (h⁻¹) ^ k •
    ∑ j : Fin (k + 1),
      ((-1 : ℝ) ^ j.1 * (Nat.choose k j.1 : ℝ)) •
        pointShift15517 (t + (j.1 : ℝ) * h)

/-- Convergence of the concrete finite-difference distributions to the actual
point-shift derivatives. -/
def finiteDifferenceDerivativeLimit15517 : Prop :=
  ∀ (t : ℝ) (k : ℕ),
    Tendsto
      (fun h : ℝ => finiteDifferenceDerivative15517 t k h)
      (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)))
      (nhds (deltaDerivative t k))

/-- Smoothness in the shift variable on an open neighborhood of the actual
compact distributional support. -/
def smoothShiftTestNearSupport15517
    (T : RealDistribution) (a : ℝ) (logZeta : ℂ → ℂ) : Prop :=
  ∀ s : ℂ, 1 - a < s.re →
    ∃ U : Set ℝ,
      IsOpen U ∧
        Distribution.dsupport T ⊆ U ∧
          ContDiffOn ℝ ⊤
            (fun α : ℝ => logZeta (s + (α : ℂ))) U

/-- Holomorphy in the complex shift parameter at every point of the actual
support. -/
def holomorphicShiftNearSupport15517
    (T : RealDistribution) (a : ℝ) (logZeta : ℂ → ℂ) : Prop :=
  ∀ α : ℝ, α ∈ Distribution.dsupport T →
    AnalyticOnNhd ℂ
      (fun s : ℂ => logZeta (s + (α : ℂ)))
      {s : ℂ | 1 - a < s.re}

/-- Claim 15517: a nonzero compactly supported real distribution admits the
canonical shifted-zeta pairing and exponential on the exact right half-plane,
with holomorphic logarithm, smooth test functions near support, point-shift
derivative specializations, and their concrete finite-difference limits. -/
def claim15517_compactDistributionShiftExponent : Prop :=
  (∀ (T : RealDistribution) (a : ℝ),
    T ≠ 0 →
      IsCompact (Distribution.dsupport T) →
        IsLeast (Distribution.dsupport T) a →
          ∃ logZeta L E : ℂ → ℂ,
            IsActualShiftedZetaLog T a logZeta L ∧
              (∀ s : ℂ, 1 - a < s.re →
                E s = shiftedZetaExponential L s) ∧
              smoothShiftTestNearSupport15517 T a logZeta ∧
                holomorphicShiftNearSupport15517 T a logZeta) ∧
    finiteDifferenceDerivativeLimit15517 ∧
      (∀ (t : ℝ) (k : ℕ),
        ∃ logZeta L E : ℂ → ℂ,
          IsActualShiftedZetaLog (deltaDerivative t k) t logZeta L ∧
            (∀ s : ℂ, 1 - t < s.re →
              E s = shiftedZetaExponential L s))

end

end MathlibPlus.Open.ResearchFormalization.O0338
