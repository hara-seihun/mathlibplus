import Mathlib
import MathlibPlus.Open.ResearchFormalization.R3267UnitLattice

namespace MathlibPlus.Open.ResearchFormalization.R3267InteriorExcess

noncomputable section
open Classical
open scoped BigOperators

/-- Physical area of the actual finite-lattice Voronoi cell at `x`. -/
def voronoiCellArea (r : ℤ)
    (x : MathlibPlus.Open.ResearchFormalization.R3267UnitLattice.Point) : ℝ :=
  ENNReal.toReal
    (MeasureTheory.volume
      (MathlibPlus.Open.ResearchFormalization.R3267UnitLattice.relativeVoronoiCell r x))

/-- Claim 46383: the actual relative Voronoi-cell areas over the exact interior
lattice have positive total excess, with the stated sharp upper bound and the
supporting scale and counting estimates. -/
def claim_46383 : Prop :=
  ∀ r : ℤ, 4 ≤ r →
    ∃ I : Finset
        MathlibPlus.Open.ResearchFormalization.R3267UnitLattice.Point,
      (∀ x : MathlibPlus.Open.ResearchFormalization.R3267UnitLattice.Point,
        x ∈ I ↔
          x ∈ MathlibPlus.Open.ResearchFormalization.R3267UnitLattice.interiorLattice r) ∧
      MathlibPlus.Open.ResearchFormalization.R3267UnitLattice.latticeS r ^ 2 -
          (3 / 4 : ℝ) =
        ((r : ℝ)⁻¹) ^ 4 - ((r : ℝ)⁻¹) ^ 8 ∧
      MathlibPlus.Open.ResearchFormalization.R3267UnitLattice.latticeS r -
          Real.sqrt 3 / 2 ≤
        2 / (Real.sqrt 3 * (r : ℝ) ^ 4) ∧
      (I.card : ℝ) ≤
        Real.pi * ((r : ℝ) - 1) ^ 2 /
          MathlibPlus.Open.ResearchFormalization.R3267UnitLattice.latticeS r ∧
      (∀ x : MathlibPlus.Open.ResearchFormalization.R3267UnitLattice.Point,
        x ∈ I → Real.sqrt 3 / 2 < voronoiCellArea r x) ∧
      0 < Finset.sum I (fun x => voronoiCellArea r x - Real.sqrt 3 / 2) ∧
      Finset.sum I (fun x => voronoiCellArea r x - Real.sqrt 3 / 2) <
        4 * Real.pi / (3 * (r : ℝ) ^ 2)

end

end MathlibPlus.Open.ResearchFormalization.R3267InteriorExcess
