import Mathlib

namespace MathlibPlus.Open.Analysis.ProjectiveLocalCrossingClaim15406

noncomputable section

open scoped Topology

/-- The crossing set of two complex-valued channels in a domain. -/
def crossingSet (D : Set ℂ) (S B : ℂ → ℂ) : Set ℂ :=
  {z | z ∈ D ∧ ‖B z‖ = ‖S z‖}

/-- The projective first-jet determinant. -/
def projectiveDeterminant (S B : ℂ → ℂ) : ℂ → ℂ :=
  fun z => S z * deriv B z - deriv S z * B z

/-- Removal of common local factors, expressed on the domain where the graph is used. -/
def commonLocalFactorsRemoved (D : Set ℂ) (S B : ℂ → ℂ) : Prop :=
  ∀ z : ℂ, z ∈ D → ¬ (S z = 0 ∧ B z = 0)

/-- The punctured local crossing set. -/
def localCrossingPoints (D : Set ℂ) (S B : ℂ → ℂ) (v : ℂ) (ρ : ℝ) : Set ℂ :=
  {z | z ∈ D ∧ z ∈ Metric.ball v ρ ∧ z ≠ v ∧ ‖B z‖ = ‖S z‖}

/-- The number of local incident half-edges, as the number of connected
components of the punctured local level graph. -/
def incidentHalfEdgeCount (D : Set ℂ) (S B : ℂ → ℂ) (v : ℂ) (ρ : ℝ) : ℕ :=
  Nat.card (ConnectedComponents {z : ℂ // z ∈ localCrossingPoints D S B v ρ})

/-- Exact analytic vanishing order at a point. -/
def exactAnalyticZeroOrder (f : ℂ → ℂ) (v : ℂ) (m : ℕ) : Prop :=
  AnalyticAt ℂ f v ∧
    (∀ k : ℕ, k < m → iteratedDeriv k f v = 0) ∧
      iteratedDeriv m f v ≠ 0

/-- Claim 15406: after common local factors are removed, a critical point of
order `m` of the projective determinant on the modulus-crossing set has the
stated local Taylor expansion and exactly the corresponding number of
incident half-edges. -/
def claim15406_localCrossingGraphDegree : Prop :=
  ∀ (D : Set ℂ) (S B : ℂ → ℂ) (v : ℂ) (m : ℕ),
    IsOpen D →
      AnalyticOnNhd ℂ S D →
        AnalyticOnNhd ℂ B D →
          commonLocalFactorsRemoved D S B →
            let Γ := crossingSet D S B
            let Δ := projectiveDeterminant S B
            let r : ℂ → ℂ := fun z => -B z / S z
            v ∈ Γ →
              Δ v = 0 →
                exactAnalyticZeroOrder Δ v m →
                  (∀ z : ℂ, z ∈ Γ → S z * B z ≠ 0) ∧
                    (∃ c : ℂ,
                      c ≠ 0 ∧
                        Asymptotics.IsBigO (𝓝 v)
                          (fun z => r z - r v - c * (z - v) ^ (m + 1))
                          (fun z => (z - v) ^ (m + 2))) ∧
                      (∃ ρ : ℝ,
                        0 < ρ ∧
                          Metric.ball v ρ ⊆ D ∧
                            Finite
                              (ConnectedComponents
                                {z : ℂ // z ∈ localCrossingPoints D S B v ρ}) ∧
                              incidentHalfEdgeCount D S B v ρ = 2 * (m + 1))

end

end MathlibPlus.Open.Analysis.ProjectiveLocalCrossingClaim15406
