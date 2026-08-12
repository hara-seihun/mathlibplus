import Mathlib

open scoped Matrix

namespace MathlibPlus.LinearAlgebra.Claim11599

/-!
The explicit zero matrix and length-two nilpotent Jordan block from claim
`11599`.  The field parameter keeps the statement independent of a choice of
characteristic; no spectral or Jordan-form hypothesis is added.
-/

theorem zeroAndNilpotentJordanBlock
    (K : Type*) [Field K] :
    let Z : Matrix (Fin 2) (Fin 2) K := 0
    let N : Matrix (Fin 2) (Fin 2) K := !![0, 1; 0, 0]
    Z.charpoly = Polynomial.X ^ 2 ∧
      N.charpoly = Polynomial.X ^ 2 ∧
      (∀ m : ℕ, 1 ≤ m → Matrix.trace (Z ^ m) = 0) ∧
      (∀ m : ℕ, 1 ≤ m → Matrix.trace (N ^ m) = 0) ∧
      Module.finrank K (LinearMap.ker (Matrix.toLin' Z)) = 2 ∧
      Module.finrank K (LinearMap.ker (Matrix.toLin' N)) = 1 ∧
      Z ^ 1 = 0 ∧
      Z ^ 0 ≠ 0 ∧
      N ^ 2 = 0 ∧
      N ^ 1 ≠ 0 := by
  dsimp only
  let Z : Matrix (Fin 2) (Fin 2) K := 0
  let N : Matrix (Fin 2) (Fin 2) K := !![0, 1; 0, 0]
  change Z.charpoly = Polynomial.X ^ 2 ∧
      N.charpoly = Polynomial.X ^ 2 ∧
      (∀ m : ℕ, 1 ≤ m → Matrix.trace (Z ^ m) = 0) ∧
      (∀ m : ℕ, 1 ≤ m → Matrix.trace (N ^ m) = 0) ∧
      Module.finrank K (LinearMap.ker (Matrix.toLin' Z)) = 2 ∧
      Module.finrank K (LinearMap.ker (Matrix.toLin' N)) = 1 ∧
      Z ^ 1 = 0 ∧
      Z ^ 0 ≠ 0 ∧
      N ^ 2 = 0 ∧
      N ^ 1 ≠ 0
  have hN2 : N ^ 2 = 0 := by
    dsimp [N]
    rw [pow_two]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two]
  have hNpow : ∀ {m : ℕ}, 2 ≤ m → N ^ m = 0 := by
    intro m hm
    have hm' : m = 2 + (m - 2) := by omega
    rw [hm', pow_add, hN2, zero_mul]
  have hkerN : LinearMap.ker (Matrix.toLin' N) = K ∙ (![1, 0] : Fin 2 → K) := by
    dsimp [N]
    let e0 : Fin 2 → K := ![1, 0]
    change LinearMap.ker (Matrix.toLin' (!![0, 1; 0, 0] : Matrix (Fin 2) (Fin 2) K)) = K ∙ e0
    have he0 : (Matrix.toLin' (!![0, 1; 0, 0] : Matrix (Fin 2) (Fin 2) K)) e0 = 0 := by
      ext i
      fin_cases i <;>
        simp [e0, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    ext v
    constructor
    · intro hv
      rw [Submodule.mem_span_singleton]
      refine ⟨v 0, ?_⟩
      funext i
      fin_cases i
      · simp [e0]
      · have hcoord := congrFun hv (0 : Fin 2)
        simp [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two] at hcoord
        simp [e0, hcoord]
    · intro hv
      rw [Submodule.mem_span_singleton] at hv
      obtain ⟨a, rfl⟩ := hv
      change (Matrix.toLin' (!![0, 1; 0, 0] : Matrix (Fin 2) (Fin 2) K)) (a • e0) = 0
      rw [map_smul, he0, smul_zero]
  have hkerZ : LinearMap.ker (Matrix.toLin' Z) = ⊤ := by
    rw [LinearMap.ker_eq_top]
    ext v
    simp [Z]
  have hkerNrank : Module.finrank K (LinearMap.ker (Matrix.toLin' N)) = 1 := by
    rw [hkerN]
    apply finrank_span_singleton
    intro h
    have h0 := congrFun h (0 : Fin 2)
    simpa using h0
  have hkerZrank : Module.finrank K (LinearMap.ker (Matrix.toLin' Z)) = 2 := by
    rw [hkerZ, finrank_top]
    simp
  have hZchar : Z.charpoly = Polynomial.X ^ 2 := by
    rw [Matrix.charpoly_fin_two]
    simp [Z, Matrix.trace_fin_two, Matrix.det_fin_two]
  have hNchar : N.charpoly = Polynomial.X ^ 2 := by
    rw [Matrix.charpoly_fin_two]
    simp [N, Matrix.trace_fin_two, Matrix.det_fin_two]
  have hZtrace : ∀ m : ℕ, 1 ≤ m → Matrix.trace (Z ^ m) = 0 := by
    intro m hm
    rw [show Z ^ m = 0 by simp [Z, zero_pow (Nat.ne_of_gt hm)]]
    simp
  have hNtrace : ∀ m : ℕ, 1 ≤ m → Matrix.trace (N ^ m) = 0 := by
    intro m hm
    have hcases : m = 1 ∨ 2 ≤ m := by omega
    rcases hcases with rfl | hm2
    · simp [N, Matrix.trace_fin_two]
    · rw [hNpow hm2]
      simp
  have hZone : Z ^ 1 = 0 := by simp [Z]
  have hZzero : Z ^ 0 ≠ 0 := by
    intro h
    have h00 := congrArg (fun A : Matrix (Fin 2) (Fin 2) K => A 0 0) h
    simp [Z, Matrix.one_apply] at h00
  have hNone : N ^ 1 ≠ 0 := by
    intro h
    have h01 := congrArg (fun A : Matrix (Fin 2) (Fin 2) K => A 0 1) h
    simp [N] at h01
  exact ⟨hZchar, hNchar, hZtrace, hNtrace, hkerZrank, hkerNrank,
    hZone, hZzero, hN2, hNone⟩

end MathlibPlus.LinearAlgebra.Claim11599
