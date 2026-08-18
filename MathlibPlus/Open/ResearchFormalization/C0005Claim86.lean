import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.C0005

noncomputable section

/-- The determinant of coordinatewise tangent rows sampled at parameters s. -/
noncomputable def tangentVolume {n : ℕ} (γ : ℝ → Fin n → ℝ)
    (s : Fin n → ℝ) : ℝ :=
  Matrix.det fun i j => deriv (fun t => γ t j) (s i)

/-- Positivity for every transversal choice from the consecutive closed gaps. -/
def pointwisePositiveOsculating {n : ℕ} (γ : ℝ → Fin n → ℝ)
    (q : Fin (n + 1) → ℝ) : Prop :=
  ∀ s : Fin n → ℝ,
    (∀ i, s i ∈ Set.Icc (q i.castSucc) (q i.succ)) →
    0 < tangentVolume γ s

/-- Claim 86: strict ordering of the knots together with pointwise positive
partition-transversal tangent orientation. -/
def claim86 {n : ℕ} (γ : ℝ → Fin n → ℝ)
    (q : Fin (n + 1) → ℝ) : Prop :=
  StrictMono q ∧ pointwisePositiveOsculating γ q

end
end MathlibPlus.Open.ResearchFormalization.C0005
