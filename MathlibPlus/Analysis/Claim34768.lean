import MathlibPlus.Open.ResearchFormalization.Claim37034

namespace MathlibPlus.Analysis.Claim34768

open MathlibPlus.Open.ResearchFormalization

noncomputable section

/-- The side-one circumradius of the regular polygon, retained from the
reviewed regular-polygon carrier. -/
def R (m : ℕ) : ℝ :=
  polygonRadius m

/-- The diameter of the actual vertex set of the reviewed regular polygon. -/
def D (m : ℕ) : ℝ :=
  diameter (polygonVertices m)

/-- Claim 34768: for an odd regular polygon of order at least three, its
geometric vertex-set diameter has the exact trigonometric formulas and the
stated correction, sine, and radius bounds. -/
def odd_polygon_diameter_claim : Prop :=
  ∀ {m : ℕ}, 3 ≤ m → Odd m →
    D m = 2 * R m * Real.cos (Real.pi / (2 * (m : ℝ))) ∧
      D m = 1 / (2 * Real.sin (Real.pi / (2 * (m : ℝ)))) ∧
      D m ^ 2 = 4 * R m ^ 2 -
        1 / (4 * Real.cos (Real.pi / (2 * (m : ℝ))) ^ 2) ∧
      1 / (4 * Real.cos (Real.pi / (2 * (m : ℝ))) ^ 2) ≤ (1 : ℝ) / 3 ∧
      Real.sin (Real.pi / (m : ℝ)) < Real.pi / (m : ℝ) ∧
      (m : ℝ) / (2 * Real.pi) < R m

end

end MathlibPlus.Analysis.Claim34768
