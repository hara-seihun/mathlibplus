import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Data.Fin.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace MathlibPlus.LinearAlgebra

/--
Claim 58154.  For a closed path in a rational vector space, the all-ones
coefficient vector annihilates the path-difference map.  The finite-dimensional
hypothesis is retained from the claim even though the telescoping proof does not
use it.
-/
theorem claim58154_unit_path_mem_kernel
    (ℓ : ℕ) {W : Type*} [AddCommGroup W] [Module ℚ W]
    [FiniteDimensional ℚ W]
    (x : Fin (ℓ + 1) → W)
    (hcycle : x (Fin.last ℓ) = x 0) :
    let pathColumn : Fin ℓ → W :=
      fun i => x (Fin.castSucc i) - x (Fin.succ i)
    let L : (Fin ℓ → ℚ) →ₗ[ℚ] W :=
      { toFun := fun q => ∑ i : Fin ℓ, q i • pathColumn i
        map_add' := by
          intro q r
          simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
        map_smul' := by
          intro a q
          simp [Pi.smul_apply, smul_eq_mul, Finset.smul_sum, smul_smul] }
    let p : Fin ℓ → ℚ := fun _ => 1
    p ∈ LinearMap.ker L := by
  dsimp
  have hsum (n : ℕ) (y : Fin (n + 1) → W) :
      (∑ i : Fin n, (y (Fin.castSucc i) - y (Fin.succ i))) =
        y 0 - y (Fin.last n) := by
    induction n with
    | zero =>
        have hzero : (Fin.last 0 : Fin 1) = 0 := by
          apply Fin.ext
          rfl
        simp [hzero]
    | succ n ih =>
        rw [Fin.sum_univ_succ]
        have htail := ih (y := fun j : Fin (n + 1) => y (Fin.succ j))
        have htail' :
            (∑ i : Fin n,
              (y (Fin.castSucc (Fin.succ i)) - y (Fin.succ (Fin.succ i)))) =
              y 1 - y (Fin.last (n + 1)) := by
          simpa using htail
        rw [htail']
        simp
  change (∑ i : Fin ℓ, (1 : ℚ) • (x (Fin.castSucc i) - x (Fin.succ i))) = 0
  simp only [one_smul]
  rw [hsum ℓ x, hcycle]
  exact sub_self _

end MathlibPlus.LinearAlgebra
