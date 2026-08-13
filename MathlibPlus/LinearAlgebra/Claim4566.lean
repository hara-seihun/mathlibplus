import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic

open Matrix

namespace MathlibPlus.LinearAlgebra

noncomputable section

/-!
Statement-fidelity formalization of admitted claim 4566 (D-0024).

The companion is represented by the standard column companion matrix of
`T^2 + 7*T + 9`, namely `[[0, -9], [1, -7]]`.  The claim says that no
positive-definite real symmetric form can make this matrix a similitude with
factor `q = 9`.
-/

/-- The `q = 9` companion Frobenius admits no positive Rosati form. -/
theorem noPositiveRosatiForm_claim4566 :
    ¬ ∃ H : Matrix (Fin 2) (Fin 2) ℝ,
      H.PosDef ∧
        let F : Matrix (Fin 2) (Fin 2) ℝ := !![0, -9; 1, -7]
        F.transpose * H * F = 9 • H := by
  rintro ⟨H, hH, hsim⟩
  have hpos := (Matrix.posDef_iff_dotProduct_mulVec.mp hH)
  have hsym := hpos.1
  have hquad := hpos.2
  dsimp at hsim
  have e00 := congrFun (congrFun hsim 0) 0
  have e01 := congrFun (congrFun hsim 0) 1
  have e10 := congrFun (congrFun hsim 1) 0
  have e11 := congrFun (congrFun hsim 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_succ] at e00 e01 e10 e11
  have hs01 : H 0 1 = H 1 0 := by
    simpa [Matrix.IsHermitian] using (congrFun (congrFun hsym 0) 1).symm
  have h00 : 0 < H 0 0 := by
    have hv := hquad (x := fun i : Fin 2 => if i = (0 : Fin 2) then 1 else 0) (by
      intro hz
      have := congrFun hz 0
      simp at this)
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_succ] using hv
  have hrelc : H 1 1 = 9 * H 0 0 := by linarith [e00]
  have hrelb : H 0 1 = -(7 / 2 : ℝ) * H 0 0 := by
    rw [hs01] at e01
    linarith [e01, hrelc]
  have hv := hquad
    (x := fun i : Fin 2 => if i = (0 : Fin 2) then (7 / 2 : ℝ) else 1) (by
      intro hz
      have := congrFun hz 1
      simp at this)
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ] at hv
  rw [show H 1 0 = H 0 1 from hs01.symm, hrelb, hrelc] at hv
  nlinarith

end

end MathlibPlus.LinearAlgebra
