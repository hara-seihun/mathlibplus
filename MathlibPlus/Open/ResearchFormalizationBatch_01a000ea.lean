import Mathlib

namespace MathlibPlus.Open.ResearchFormalizationBatch

open scoped BigOperators
noncomputable section

/-- The character of the `k`th two-dimensional torus representation. -/
def chi (k : ℕ) (z : ℂˣ) : ℂ :=
  Finset.sum (Finset.range (k + 1)) (fun i =>
    (z : ℂ) ^ ((k : ℤ) - 2 * (i : ℤ)))

/-- The full mixed character agrees with the two alignment characters in degree one,
    but is not their sum in any degree at least two. -/
def claim7888 : Prop :=
  (∀ y α : ℂˣ,
    chi 1 y * chi 1 α = chi 1 (y * α) + chi 1 (y / α)) ∧
    (∀ k : ℕ, 2 ≤ k →
      (fun y α : ℂˣ => chi k y * chi k α) ≠
        (fun y α : ℂˣ => chi k (y * α) + chi k (y / α)))

abbrev Matrix2 := Matrix (Fin 2) (Fin 2) ℂ

def pauliI : Matrix2 := !![1, 0; 0, 1]
def pauliX : Matrix2 := !![0, 1; 1, 0]
def pauliZ : Matrix2 := !![1, 0; 0, -1]
def pauliIY : Matrix2 := !![0, 1; -1, 0]
def cuspProjector : Matrix2 := (1 / 2 : ℂ) • (pauliI - pauliZ)
def rightProjection (A : Matrix2) : Matrix2 := A * cuspProjector

/-- Right multiplication by the cusp projector on the Pauli coefficient algebra. -/
def claim7892 : Prop :=
  Module.finrank ℂ Matrix2 = 4 ∧
    Module.finrank ℂ
      (Submodule.span ℂ (Set.range rightProjection)) = 2 ∧
    (∀ A : Matrix2,
      rightProjection A = 0 ↔
        A ∈ Submodule.span ℂ
          ({pauliI + pauliZ, pauliX - pauliIY} : Set Matrix2)) ∧
    rightProjection pauliI = rightProjection (-pauliZ) ∧
    rightProjection pauliX = rightProjection pauliIY

end
end MathlibPlus.Open.ResearchFormalizationBatch
