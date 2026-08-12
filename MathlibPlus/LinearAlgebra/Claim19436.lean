import Mathlib

open scoped BigOperators

namespace MathlibPlus.LinearAlgebra.Claim19436

/-- Scaling every column outside a fixed maximal-minor index by `ε` scales a
maximal minor by one factor of `ε` for each selected outside column. -/
theorem columnTorusScaling_maximalMinor
    {R : Type*} [CommRing R] {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) R) (ε : R)
    (M₀ M : Fin m ↪ Fin n) :
    let Aε : Matrix (Fin m) (Fin n) R :=
      fun i j => if j ∈ Set.range M₀ then A i j else ε * A i j
    let outside : Finset (Fin m) :=
      Finset.univ.filter (fun i => M i ∉ Set.range M₀)
    (Aε.submatrix id M).det =
        ε ^ outside.card * (A.submatrix id M).det ∧
      (Aε.submatrix id M₀).det = (A.submatrix id M₀).det := by
  dsimp
  let d : Fin n → R := fun j => if j ∈ Set.range M₀ then 1 else ε
  constructor
  · have hsub :
        Matrix.submatrix
            (fun i j => if j ∈ Set.range M₀ then A i j else ε * A i j)
            id M =
          Matrix.of (fun i j => d (M j) * (A.submatrix id M) i j) := by
      ext i j
      simp [d, Matrix.submatrix]
    rw [hsub, Matrix.det_mul_row]
    have hprod : (∏ i : Fin m, d (M i)) = ε ^
        (Finset.univ.filter (fun i => M i ∉ Set.range M₀)).card := by
      classical
      have hpoint : ∀ i : Fin m,
          d (M i) = if M i ∉ Set.range M₀ then ε else 1 := by
        intro i
        by_cases h : M i ∈ Set.range M₀
        · have hnot : ¬ M i ∉ Set.range M₀ := not_not_intro h
          simp only [d, if_pos h, if_neg hnot]
        · simp only [d, if_neg h, if_pos h]
      calc
        (∏ i : Fin m, d (M i)) =
            ∏ i : Fin m, if M i ∉ Set.range M₀ then ε else 1 := by
              apply Finset.prod_congr rfl
              intro i hi
              exact hpoint i
        _ = ε ^ (Finset.univ.filter (fun i => M i ∉ Set.range M₀)).card := by
              rw [← Finset.prod_filter]
              simp
    rw [hprod]
  · have hsub :
        Matrix.submatrix
            (fun i j => if j ∈ Set.range M₀ then A i j else ε * A i j)
            id M₀ = A.submatrix id M₀ := by
      ext i j
      simp [Matrix.submatrix, Set.mem_range]
    rw [hsub]

end MathlibPlus.LinearAlgebra.Claim19436
