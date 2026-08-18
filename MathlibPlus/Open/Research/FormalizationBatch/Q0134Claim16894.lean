import MathlibPlus.Open.ResearchFormalization.BatchQ0134Claim16879

namespace MathlibPlus.Open.Research.FormalizationBatch.Q0134Claim16894

open MathlibPlus.Open.ResearchFormalization.BatchQ0134Claim16879
open Classical

noncomputable section

/-- The four-coordinate lift of a planar point used by the squared-distance
matrix columns. -/
def liftedVector16894 (p : Plane) : Fin 4 → ℝ :=
  fun i =>
    if i = 0 then ‖p‖ ^ 2
    else if i = 1 then p 0
    else if i = 2 then p 1
    else 1

/-- The affine hyperplane containing lifts of a circle with physical apex v
and radius r. -/
def apexCircleHyperplane16894
    (v : Plane) (r : ℝ) (w : Fin 4 → ℝ) : Prop :=
  w 0 - 2 * v 0 * w 1 - 2 * v 1 * w 2 +
      (‖v‖ ^ 2 - r ^ 2) * w 3 = 0

/-- The span of the selected columns of a finite matrix. -/
def selectedColumnSpan16894 {n : ℕ}
    (L : Matrix (Fin n) (Fin n) ℝ) (C : Finset (Fin n)) :
    Submodule ℝ (Fin n → ℝ) :=
  Submodule.span ℝ
    (Set.range (fun j : {j : Fin n // j ∈ C} =>
      fun i : Fin n => L i j.1))

/-- A retained circle class gives the apex-circle lift hyperplane and the
rank-three bound for the corresponding columns of the directed residual
matrix. -/
def retainedCircleRankThree_claim16894 : Prop :=
  ∀ (n : ℕ) (P : Finset Plane) (p : Fin n → Plane)
    (rho : Fin n → ℝ) (L : Matrix (Fin n) (Fin n) ℝ),
    (∀ i : Fin n, p i ∈ P) →
    Function.Injective p →
    P = (Finset.univ : Finset (Fin n)).image p →
    (∀ i j : Fin n,
      L i j = ‖p i - p j‖ ^ 2 - rho i) →
    ∀ (v : Plane) (r : ℝ) (C : Finset (Fin n)),
      v ∈ P →
      0 < r →
      (∀ j : Fin n, j ∈ C → p j ∈ radiusClass P v r) →
      (∀ j : Fin n, j ∈ C →
        apexCircleHyperplane16894 v r (liftedVector16894 (p j))) ∧
        Module.finrank ℝ (selectedColumnSpan16894 L C) ≤ 3

end

end MathlibPlus.Open.Research.FormalizationBatch.Q0134Claim16894
