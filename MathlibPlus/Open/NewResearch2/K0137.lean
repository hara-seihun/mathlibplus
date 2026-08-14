import Mathlib

namespace MathlibPlus.Open.NewResearch2.K0137

/-- Degree computed by filtering the finite ambient vertex carrier. -/
noncomputable def graphDegree {V : Type*} [Fintype V]
    (G : SimpleGraph V) (u : V) : ℕ := by
  classical
  exact (Finset.univ.filter (fun v => G.Adj u v)).card

/-- The degree layer of a finite graph. -/
noncomputable def degreeLayerCount {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (d : ℕ) : ℕ :=
  (Finset.univ.filter (fun u => graphDegree G u = d)).card

/-- The old-vertex degree layer after designating `w` as the missing vertex. -/
noncomputable def oldDegreeLayerCount {V : Type*} [Fintype V] [DecidableEq V]
    (C : SimpleGraph V) (w : V) (d : ℕ) : ℕ :=
  (Finset.univ.filter (fun u => u ≠ w ∧ graphDegree C u = d)).card

/-- The attached old vertices which leave degree layer `d`. -/
noncomputable def attachedDegreeLayerCount {V : Type*} [Fintype V] [DecidableEq V]
    (C : SimpleGraph V) (w : V) (X : Finset V) (d : ℕ) : ℕ :=
  (Finset.univ.filter (fun u => u ≠ w ∧ u ∈ X ∧ graphDegree C u = d)).card

/--
Claim 9078.  The carrier explicitly records a one-vertex attachment: `w` is
new, `X` is the set of attached old vertices, and each attached old vertex
moves up one degree layer.  Counts are compared in `ℤ`, so the displayed
`x_d` and `x_{d-1}` balance is not hidden behind truncated natural subtraction;
the `d = 0` branch is the stated convention `x_{-1} = 0`.
-/
def claim9078_degreeLayerBalanceEquation : Prop :=
  ∀ {V : Type*} [Fintype V] [DecidableEq V]
    (C G : SimpleGraph V) (w : V) (X : Finset V) (k : ℕ),
    w ∉ X →
      (∀ u, u ≠ w →
        graphDegree G u = graphDegree C u + (if u ∈ X then 1 else 0)) →
      graphDegree G w = k →
      ∀ d : ℕ,
        (degreeLayerCount G d : ℤ) =
          (if k = d then (1 : ℤ) else 0) +
            (oldDegreeLayerCount C w d : ℤ) -
            (attachedDegreeLayerCount C w X d : ℤ) +
            (if d = 0 then (0 : ℤ)
             else (attachedDegreeLayerCount C w X (d - 1) : ℤ))

end MathlibPlus.Open.NewResearch2.K0137
