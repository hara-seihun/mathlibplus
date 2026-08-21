-- UNVERIFIED (native-decide): submitted but not kernel-verified, so it is a root of the Unverified library rather than of MathlibPlus and no build here depends on it. See unverified.txt.
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

namespace MathlibPlus.Algebra.Claim29016

open Matrix

/-- Every nonidentity order-three linear action on `𝔽₂²` is fixed-point-free;
its displacement map is bijective.  The matrix formulation makes the finite
field and the two-dimensional action explicit. -/
theorem fixedPointFreeOrderThreeMatrix :
    ∀ M : Matrix (Fin 2) (Fin 2) (ZMod 2),
      M * M * M = (1 : Matrix (Fin 2) (Fin 2) (ZMod 2)) →
      M ≠ (1 : Matrix (Fin 2) (Fin 2) (ZMod 2)) →
      (∀ v : Fin 2 → ZMod 2, M.mulVec v = v → v = 0) ∧
        Function.Bijective (fun v : Fin 2 → ZMod 2 => M.mulVec v - v) := by
  native_decide

end MathlibPlus.Algebra.Claim29016
