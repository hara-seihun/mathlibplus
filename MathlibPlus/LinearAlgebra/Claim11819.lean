import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.Nat.Squarefree
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic

open Matrix

namespace MathlibPlus.LinearAlgebra.Claim11819

/-- The concrete common-place-weight tensor witness from packet O-0158.  The
ordered product index `(Fin 2 × Fin 2)` is the tensor-product basis order; the
last conjunct gives the exact two-free-coordinate description of the global
kernel. -/
theorem commonPlaceWeightCounterexample (p q : ℕ)
    (hp : Nat.Prime p) (hq : Nat.Prime q) (hpq : p ≠ q) :
    let H : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]
    let I2 : Matrix (Fin 2) (Fin 2) ℂ := 1
    let K : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
      Matrix.kronecker H I2 + Matrix.kronecker I2 H
    let d : (Fin 2 × Fin 2) → ℂ :=
      fun ij => if ij = (0, 0) then 2 else if ij = (1, 1) then -2 else 0
    let w : ℂ → ℂ → (Fin 2 × Fin 2) → ℂ :=
      fun a b ij => if ij = (0, 1) then a else if ij = (1, 0) then b else 0
    Squarefree (p * q) ∧
      H.det ≠ 0 ∧
      K = Matrix.diagonal d ∧
      ∀ v : (Fin 2 × Fin 2) → ℂ,
        K *ᵥ v = 0 ↔ ∃ a b : ℂ, v = w a b := by
  dsimp
  let H : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]
  let I2 : Matrix (Fin 2) (Fin 2) ℂ := 1
  let K : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
    Matrix.kronecker H I2 + Matrix.kronecker I2 H
  let d : (Fin 2 × Fin 2) → ℂ :=
    fun ij => if ij = (0, 0) then 2 else if ij = (1, 1) then -2 else 0
  let w : ℂ → ℂ → (Fin 2 × Fin 2) → ℂ :=
    fun a b ij => if ij = (0, 1) then a else if ij = (1, 0) then b else 0
  change Squarefree (p * q) ∧
      H.det ≠ 0 ∧
      K = Matrix.diagonal d ∧
      ∀ v : (Fin 2 × Fin 2) → ℂ,
        K *ᵥ v = 0 ↔ ∃ a b : ℂ, v = w a b
  have hsq : Squarefree (p * q) := by
    apply (Nat.squarefree_mul ((Nat.coprime_primes hp hq).mpr hpq)).mpr
    exact ⟨hp.squarefree, hq.squarefree⟩
  have hdet : H.det ≠ 0 := by
    norm_num [H, Matrix.det_fin_two]
  have hK : K = Matrix.diagonal d := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [K, H, I2, d, Matrix.kroneckerMap_apply, Matrix.diagonal_apply]
  refine ⟨hsq, hdet, hK, ?_⟩
  intro v
  constructor
  · intro hv
    have h00 : v (0, 0) = 0 := by
      simpa [hK, Matrix.mulVec_diagonal, d] using congrFun hv (0, 0)
    have h11 : v (1, 1) = 0 := by
      simpa [hK, Matrix.mulVec_diagonal, d] using congrFun hv (1, 1)
    refine ⟨v (0, 1), v (1, 0), ?_⟩
    funext i
    fin_cases i <;> simp [w, h00, h11]
  · rintro ⟨a, b, rfl⟩
    rw [hK]
    funext i
    fin_cases i <;> simp [Matrix.mulVec_diagonal, d, w]

end MathlibPlus.LinearAlgebra.Claim11819
