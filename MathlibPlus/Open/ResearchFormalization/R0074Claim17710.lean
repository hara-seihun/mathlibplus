import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.R0074Claim17710

noncomputable section

/-- The positive real carrier on which the source moment family is defined. -/
abbrev PositiveReal := {X : ℝ // 0 < X}

/-- The positive integer carrier on which the source defect is defined. -/
abbrev PositiveLevel := {n : ℕ // 1 ≤ n}

/-- The exact lattice spline moment from the source. -/
noncomputable def latticeSplineMoment (r : ℕ) (X : PositiveReal) : ℝ :=
  (1 / (Nat.factorial r : ℝ)) *
    ∑ m ∈ Finset.Icc 1 ⌊(X : ℝ)⌋₊,
      (m : ℝ) ^ (-1 / 2 : ℝ) *
        (Real.log ((X : ℝ) / (m : ℝ))) ^ r

/-- The Mellin-continuum moment appearing in the source subtraction. -/
noncomputable def continuumSplineMoment (r : ℕ) (X : PositiveReal) : ℝ :=
  (2 : ℝ) ^ (r + 1) * Real.sqrt (X : ℝ)

/-- The exact normalized defect port. -/
noncomputable def defectPort (n : PositiveLevel) (X : PositiveReal) : ℝ :=
  Real.rpow Real.pi (-1 / 4 : ℝ) *
    (latticeSplineMoment (2 * n.1 - 2) X -
      latticeSplineMoment (2 * n.1) X / 4)

/-- Claim 17710: the continuum quarter-shift vanishes and the same defect is
exactly the lattice-minus-continuum quadrature error after that shift. -/
def claim17710_materialDefectIsQuadratureError : Prop :=
  ∀ (n : PositiveLevel) (X : PositiveReal),
    let c : ℝ := Real.rpow Real.pi (-1 / 4 : ℝ)
    c *
          (continuumSplineMoment (2 * n.1 - 2) X -
            continuumSplineMoment (2 * n.1) X / 4) = 0 ∧
      defectPort n X =
        c *
          (latticeSplineMoment (2 * n.1 - 2) X -
            latticeSplineMoment (2 * n.1) X / 4) ∧
      defectPort n X =
        c *
          ((latticeSplineMoment (2 * n.1 - 2) X -
              continuumSplineMoment (2 * n.1 - 2) X) -
            (latticeSplineMoment (2 * n.1) X -
              continuumSplineMoment (2 * n.1) X) / 4)

end

end MathlibPlus.Open.ResearchFormalization.R0074Claim17710
