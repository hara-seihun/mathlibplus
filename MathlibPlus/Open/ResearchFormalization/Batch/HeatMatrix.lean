import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.Batch.HeatMatrix

noncomputable def heatU {r : ℕ} (q l : Fin r → ℝ) (a : ℝ) :
    Matrix (Fin r) (Fin r) ℝ :=
  fun i j => Real.rpow (l j) (-a) * Real.exp (-q i / l j)

noncomputable def heatV {r : ℕ} (q l : Fin r → ℝ) (a : ℝ) :
    Matrix (Fin r) (Fin r) ℝ :=
  fun i j => Real.rpow (l j) a * Real.exp (-q i * l j)

noncomputable def alternatingDiagonal (r : ℕ) : Matrix (Fin r) (Fin r) ℝ :=
  Matrix.diagonal (fun i => (-1 : ℝ) ^ i.val)

noncomputable def transitionMatrix {r : ℕ} (q l : Fin r → ℝ) (a : ℝ) :
    Matrix (Fin r) (Fin r) ℝ :=
  alternatingDiagonal r * (heatU q l a)⁻¹ * heatV q l a

def heatOrdering {r : ℕ} (q l : Fin r → ℝ) : Prop :=
  StrictMono q ∧ StrictMono l ∧ ∀ i : Fin r, 1 < l i

noncomputable def principalDet {r : ℕ}
    (M : Matrix (Fin r) (Fin r) ℝ) (S : Finset (Fin r)) : ℝ :=
  (M.submatrix
    (fun i : {x // x ∈ S} => (i : Fin r))
    (fun i : {x // x ∈ S} => (i : Fin r))).det

noncomputable def minorDet {r k : ℕ}
    (M : Matrix (Fin r) (Fin r) ℝ)
    (e f : Fin k → Fin r) : ℝ :=
  (M.submatrix e f).det

def strictlyTotallyPositive {r : ℕ}
    (M : Matrix (Fin r) (Fin r) ℝ) : Prop :=
  ∀ k : ℕ, ∀ e f : Fin k → Fin r,
    StrictMono e → StrictMono f → 0 < minorDet M e f

noncomputable def replaceColumns {r : ℕ}
    (U V : Matrix (Fin r) (Fin r) ℝ) (S : Finset (Fin r)) :
    Matrix (Fin r) (Fin r) ℝ :=
  fun i j => if j ∈ S then V i j else U i j

noncomputable def signedPrincipalMinorSum {r : ℕ}
    (B : Matrix (Fin r) (Fin r) ℝ) : ℝ :=
  ∑ S ∈ (Finset.univ : Finset (Fin r)).powerset,
    (-1 : ℝ) ^ (∑ j ∈ S, j.val) * principalDet B S

/-- Claim 2859: the exact column-replacement determinant identity. -/
def claim2859 : Prop :=
  ∀ (r : ℕ) (q l : Fin r → ℝ) (a : ℝ) (S : Finset (Fin r)),
    heatOrdering q l →
    let U := heatU q l a
    let V := heatV q l a
    let B := transitionMatrix q l a
    (replaceColumns U V S).det =
      (-1 : ℝ) ^ (∑ j ∈ S, j.val) * U.det * principalDet B S

/-- Claim 2861: determinant compression and the complete signed principal-minor sum. -/
def claim2861 : Prop :=
  ∀ (r : ℕ) (q l : Fin r → ℝ) (a : ℝ),
    heatOrdering q l →
    let U := heatU q l a
    let V := heatV q l a
    let D := alternatingDiagonal r
    let B := transitionMatrix q l a
    U.det ≠ 0 ∧
      strictlyTotallyPositive B ∧
      (U + V).det = U.det * (1 + U⁻¹ * V).det ∧
      (U + V).det = U.det * (1 + D * B).det ∧
      (1 + D * B).det = signedPrincipalMinorSum B

end MathlibPlus.Open.ResearchFormalization.Batch.HeatMatrix
