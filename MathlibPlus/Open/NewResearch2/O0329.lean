import Mathlib

open scoped ENNReal lp Topology

namespace MathlibPlus.Open.NewResearch2.O0329

noncomputable section

/-- The real Hilbert `ℓ²(ℕ)` carrier. -/
abbrev HilbertL2 := lp (fun _ : ℕ => ℝ) (2 : ℝ≥0∞)

/-- The standard coordinate vector in real `ℓ²(ℕ)`. -/
noncomputable def standardBasisVector (j : ℕ) : HilbertL2 :=
  lp.single (2 : ℝ≥0∞) j (1 : ℝ)

/-- The coordinate rank-one projection `P_j x = ⟪x,e_j⟫ e_j`. -/
def coordinateProjection (j : ℕ) (x : HilbertL2) : HilbertL2 :=
  (inner ℝ x (standardBasisVector j)) • standardBasisVector j

/-- Claim 15500: the standard coordinate projections converge to zero in
weak operator topology, expressed by their fixed matrix coefficients. -/
def claim15500 : Prop :=
  ∀ x y : HilbertL2,
    Filter.Tendsto
      (fun j : ℕ => inner ℝ (coordinateProjection j x) y)
      Filter.atTop (nhds 0)

end

end MathlibPlus.Open.NewResearch2.O0329
