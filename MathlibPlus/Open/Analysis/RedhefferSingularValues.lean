import Mathlib

namespace MathlibPlus.Open.Analysis.RedhefferSingularValues

private def oneBased {n : ℕ} (i : Fin n) : ℕ := i.val + 1

def redhefferD (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => if oneBased i ∣ oneBased j then 1 else 0

def redhefferA (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => if oneBased i ∣ oneBased j ∨ oneBased j = 1 then 1 else 0

noncomputable def redhefferB (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  (redhefferD n)⁻¹ * redhefferA n

noncomputable def redhefferSingularValue (n : ℕ) (i : Fin n) : ℝ :=
  (Matrix.toEuclideanLin (redhefferB n)).singularValues i

def all_but_two_singular_values_equal_one : Prop :=
  ∀ n : ℕ, 0 < n →
    (Finset.univ.filter (fun i : Fin n => redhefferSingularValue n i ≠ 1)).card ≤ 2

end MathlibPlus.Open.Analysis.RedhefferSingularValues
