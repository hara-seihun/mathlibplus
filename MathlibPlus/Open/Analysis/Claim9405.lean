import MathlibPlus.Open.Analysis.O0313ForcedRootReflection

namespace MathlibPlus.Open.Analysis.Claim9405

noncomputable section

/-- The noncentral points of the forced vertical preimage progression in the
Cayley disk coordinate. -/
def forcedVerticalPoint (q : ℤ) (k : ℤ) : ℂ :=
  (1 : ℂ) -
    ((1 : ℂ) -
      (2 : ℂ) * (Real.pi : ℂ) * (k : ℂ) * Complex.I /
        (Real.log (q : ℝ) : ℂ))⁻¹

/-- Claim 9405: the forced Blaschke factor splits into the central zero and
an inner factor whose zeros are exactly the noncentral forced progression. -/
def claim9405 : Prop :=
  ∀ q : ℤ, 2 ≤ q →
    let L : ℝ := Real.log (q : ℝ)
    let r : ℝ := (q : ℝ) ^ (-1 / 2 : ℝ)
    let Φq : ℂ → ℂ :=
      MathlibPlus.Open.Analysis.O0313ForcedRootReflection.geometricPhi q
    let b : ℂ → ℂ := fun u =>
      (u - (r : ℂ)) / (1 - (r : ℂ) * u)
    ∃ J : ℂ → ℂ,
      MathlibPlus.Open.Analysis.O0313ForcedRootReflection.innerOnUnitDisk J ∧
      (∀ z : ℂ, ‖z‖ < 1 →
        Φq z - (r : ℂ) =
          b (Φq z) * (1 - (r : ℂ) * Φq z)) ∧
      (∀ z : ℂ, ‖z‖ < 1 →
        b (Φq z) = z * J z) ∧
      (∀ z : ℂ, ‖z‖ < 1 → z ≠ 0 →
        J z = b (Φq z) / z) ∧
      AnalyticAt ℂ (fun z : ℂ => b (Φq z)) 0 ∧
      (fun z : ℂ => b (Φq z)) 0 = 0 ∧
      deriv (fun z : ℂ => b (Φq z)) 0 ≠ 0 ∧
      (∀ z : ℂ, ‖z‖ < 1 →
        (J z = 0 ↔
          ∃ k : ℤ, k ≠ 0 ∧ z = forcedVerticalPoint q k)) ∧
      ‖J 0‖ = L * r / (1 - r ^ 2) ∧
      -Real.log ‖J 0‖ = Real.log ((1 - r ^ 2) / (L * r)) ∧
      Real.log ((1 - r ^ 2) / (L * r)) =
        Real.log (Real.sinh (L / 2) / (L / 2))

end

end MathlibPlus.Open.Analysis.Claim9405
