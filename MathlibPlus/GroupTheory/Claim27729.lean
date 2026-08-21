-- UNVERIFIED (native-decide): submitted but not kernel-verified, so it is not built and MathlibPlus.lean does not import it. See unverified.txt.
import MathlibPlus.Basic

namespace MathlibPlus.GroupTheory.Claim27729

/-- The cardinality comparison used by the four-point `PG(1,3)` warning. -/
theorem automorphismAndAffineOrderArithmetic :
    let GL₂₃ := Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)
    let AffineParameter := (Fin 2 → ZMod 3) × GL₂₃
    Fintype.card (Equiv.Perm (Fin 9)) = 362880 ∧
      Fintype.card GL₂₃ = 48 ∧
      Fintype.card AffineParameter = 432 ∧
      432 < Fintype.card (Equiv.Perm (Fin 9)) := by
  dsimp
  have hAut : Fintype.card (Equiv.Perm (Fin 9)) = 362880 := by
    rw [Fintype.card_perm, Fintype.card_fin]
    decide
  have hGL : Fintype.card (Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) = 48 := by
    native_decide
  have hAffine :
      Fintype.card ((Fin 2 → ZMod 3) × Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) =
        432 := by
    native_decide
  refine ⟨hAut, hGL, hAffine, ?_⟩
  rw [hAut]
  norm_num

end MathlibPlus.GroupTheory.Claim27729
