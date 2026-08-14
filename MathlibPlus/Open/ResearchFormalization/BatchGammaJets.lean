import Mathlib

open scoped BigOperators
open MeasureTheory

namespace MathlibPlus.Open.ResearchFormalization

noncomputable def gammaJetKernel (α : ℝ) (p : ℕ) (v : ℝ) : ℝ :=
  2 * Real.rpow v (2 * (p : ℝ) + 2 * α - 1) * Real.exp (-(v ^ 2)) / Real.Gamma α

noncomputable def risingFactorialReal (α : ℝ) (m : ℕ) : ℝ :=
  Finset.prod (Finset.range m) (fun k => α + (k : ℝ))

noncomputable def completedEvenGammaJet (α : ℝ) (p q : ℕ) : ℝ :=
  ((Nat.factorial (2 * q) : ℝ)⁻¹) *
    (∫ v in Set.Ici (0 : ℝ), v ^ (2 * q) * gammaJetKernel α p v)

def completedEvenJetRealizationClaim (α : ℝ) : Prop :=
  ∀ p q : ℕ,
    completedEvenGammaJet α p q =
      risingFactorialReal α (p + q) * (Nat.factorial (2 * q) : ℝ)⁻¹

end MathlibPlus.Open.ResearchFormalization
