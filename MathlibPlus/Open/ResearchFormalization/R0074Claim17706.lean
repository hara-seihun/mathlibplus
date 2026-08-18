import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.R0074Claim17706

noncomputable section

/-- The positive real carrier on which the source moment family is defined. -/
abbrev PositiveReal := {X : ℝ // 0 < X}

/-- The positive integer carrier on which the two local ports are defined. -/
abbrev PositiveLevel := {n : ℕ // 1 ≤ n}

/-- The exact lattice spline moment on the source carrier. -/
noncomputable def latticeSplineMoment (r : ℕ) (X : PositiveReal) : ℝ :=
  (1 / (Nat.factorial r : ℝ)) *
    ∑ m ∈ Finset.Icc 1 ⌊(X : ℝ)⌋₊,
      (m : ℝ) ^ (-1 / 2 : ℝ) *
        (Real.log ((X : ℝ) / (m : ℝ))) ^ r

/-- The defect port with the source's affine quarter shift and normalization. -/
noncomputable def defectPort (n : PositiveLevel) (X : PositiveReal) : ℝ :=
  Real.rpow Real.pi (-1 / 4 : ℝ) *
    (latticeSplineMoment (2 * n.1 - 2) X -
      latticeSplineMoment (2 * n.1) X / 4)

/-- The companion port paired with the defect port. -/
noncomputable def companionPort (n : PositiveLevel) (X : PositiveReal) : ℝ :=
  Real.rpow Real.pi (-1 / 4 : ℝ) *
    (((n.1 - 1 : ℕ) : ℝ) * latticeSplineMoment (2 * n.1 - 2) X -
      (n.1 : ℝ) * latticeSplineMoment (2 * n.1) X / 4)

/-- The paired local port state on its exact source carrier. -/
noncomputable def localPorts (n : PositiveLevel) (X : PositiveReal) : ℝ × ℝ :=
  (defectPort n X, companionPort n X)

/-- Claim 17706: the two displayed local ports, with both source domains kept. -/
def claim17706_defectAndCompanionPorts : Prop :=
  ∀ (n : PositiveLevel) (X : PositiveReal),
    (localPorts n X).1 =
        Real.rpow Real.pi (-1 / 4 : ℝ) *
          (latticeSplineMoment (2 * n.1 - 2) X -
            latticeSplineMoment (2 * n.1) X / 4) ∧
      (localPorts n X).2 =
        Real.rpow Real.pi (-1 / 4 : ℝ) *
          (((n.1 - 1 : ℕ) : ℝ) *
              latticeSplineMoment (2 * n.1 - 2) X -
            (n.1 : ℝ) * latticeSplineMoment (2 * n.1) X / 4)

end

end MathlibPlus.Open.ResearchFormalization.R0074Claim17706
