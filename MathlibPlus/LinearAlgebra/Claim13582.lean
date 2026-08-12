import Mathlib

namespace MathlibPlus.LinearAlgebra.Claim13582

/-- Claim 13582: equal determinant order does not determine the zero module.
The diagonal and length-two nilpotent Jordan families have the same determinant
`t^2`, but their zero-specialization kernels have dimensions two and one. -/
theorem equalDeterminantOrderDoesNotDetermineZeroModule_claim13582
    {K : Type*} [Field K] :
    (∀ t : K,
      Matrix.det (!![t, 0; 0, t] : Matrix (Fin 2) (Fin 2) K) = t ^ 2 ∧
      Matrix.det (!![t, 1; 0, t] : Matrix (Fin 2) (Fin 2) K) = t ^ 2) ∧
    let zero : Matrix (Fin 2) (Fin 2) K := 0
    let jordan : Matrix (Fin 2) (Fin 2) K := !![0, 1; 0, 0]
    Module.finrank K (LinearMap.ker (Matrix.mulVecLin zero)) = 2 ∧
      Module.finrank K (LinearMap.ker (Matrix.mulVecLin jordan)) = 1 ∧
      jordan ≠ 0 ∧ jordan ^ 2 = 0 := by
  constructor
  · intro t
    constructor <;> simp [Matrix.det_fin_two, pow_two]
  · let zero : Matrix (Fin 2) (Fin 2) K := 0
    let jordan : Matrix (Fin 2) (Fin 2) K := !![0, 1; 0, 0]
    let e0 : Fin 2 → K := Pi.single (0 : Fin 2) 1
    have hjordan_kernel :
        LinearMap.ker (Matrix.mulVecLin jordan) = K ∙ e0 := by
      ext x
      constructor
      · intro hx
        have hx0 : jordan.mulVec x 0 = 0 := by
          have h := (LinearMap.mem_ker.mp hx)
          exact congrFun h 0
        have hx1 : x 1 = 0 := by
          simpa [jordan, Matrix.mulVec, Fin.sum_univ_two,
            Matrix.vecHead, Matrix.vecTail] using hx0
        rw [Submodule.mem_span_singleton]
        refine ⟨x 0, ?_⟩
        funext i
        fin_cases i
        · simp [e0]
        · simp [e0, hx1]
      · intro hx
        rw [Submodule.mem_span_singleton] at hx
        rcases hx with ⟨a, rfl⟩
        apply LinearMap.mem_ker.mpr
        funext i
        fin_cases i <;>
          simp [Matrix.mulVecLin_apply, jordan, e0, Matrix.mulVec,
            Fin.sum_univ_two]
    have hzero_kernel :
        LinearMap.ker (Matrix.mulVecLin zero) = (⊤ : Submodule K (Fin 2 → K)) := by
      rw [LinearMap.ker_eq_top]
      apply LinearMap.ext
      intro x
      simp [zero, Matrix.mulVecLin_apply]
    have hzero_dim : Module.finrank K (LinearMap.ker (Matrix.mulVecLin zero)) = 2 := by
      rw [hzero_kernel]
      simpa using (Module.finrank_fin_fun K (n := 2))
    have hjordan_dim : Module.finrank K (LinearMap.ker (Matrix.mulVecLin jordan)) = 1 := by
      rw [hjordan_kernel]
      exact finrank_span_singleton (by
        intro h
        have h0 := congrFun h 0
        simp [e0] at h0)
    have hjordan_ne : jordan ≠ 0 := by
      intro h
      have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) K => M 0 1) h
      norm_num [jordan] at h01
    have hjordan_sq : jordan ^ 2 = 0 := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        norm_num [jordan, pow_two, Matrix.mul_apply, Fin.sum_univ_two]
    simpa [zero, jordan] using
      And.intro hzero_dim (And.intro hjordan_dim (And.intro hjordan_ne hjordan_sq))

end MathlibPlus.LinearAlgebra.Claim13582
