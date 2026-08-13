import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.Matrix.Block

namespace MathlibPlus.Combinatorics.Claim9462

/-- The complete-graph complementary-pair obstruction: an undirected edge
subset cannot omit every edge at one vertex while its complement omits every
edge at a distinct vertex. -/
theorem completeGraphComplementaryPair_impossible
    {V : Type*} (A : V → V → Prop) {u v : V} (huv : u ≠ v)
    (hsymm : ∀ a b, A a b ↔ A b a)
    (hmiss : ∀ w, w ≠ u → ¬ A u w)
    (hcomp : ∀ w, w ≠ v → A v w) : False := by
  have huv' : ¬ A u v := hmiss v (Ne.symm huv)
  have hvu : A v u := hcomp u huv
  exact huv' ((hsymm u v).mpr hvu)

end MathlibPlus.Combinatorics.Claim9462

namespace MathlibPlus.LinearAlgebra.Claim4079

/-- The linear-algebra core of grafting/pruning duality: the transpose (dual)
of a surjective finite-dimensional operator is injective. -/
theorem dual_pruning_injective
    {R M N : Type*} [CommSemiring R]
    [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N]
    (prune : M →ₗ[R] N) (hprune : Function.Surjective prune) :
    Function.Injective prune.dualMap :=
  LinearMap.dualMap_injective_of_surjective hprune

end MathlibPlus.LinearAlgebra.Claim4079

namespace MathlibPlus.LinearAlgebra.Claim17235

/-- The lower-triangular cumulative-sum matrix has unit determinant. -/
theorem cumulativeSumMatrix_structure (N : ℕ) :
    Matrix.IsLowerTriangular (fun r s : Fin N => if s ≤ r then (1 : ℚ) else 0) ∧
      Matrix.det (fun r s : Fin N => if s ≤ r then (1 : ℚ) else 0) = 1 := by
  let C : Matrix (Fin N) (Fin N) ℚ :=
    fun r s => if s ≤ r then 1 else 0
  have htri : C.IsLowerTriangular := by
    intro i j hij
    change (if j ≤ i then (1 : ℚ) else 0) = 0
    have hij' : i < j := hij
    simp [not_le_of_gt hij']
  change C.IsLowerTriangular ∧ C.det = 1
  exact ⟨htri, by
    rw [Matrix.det_of_isLowerTriangular C htri]
    simp [C]⟩

/-- The unit determinant gives the claimed invertibility of the cumulative-sum
matrix over the rationals. -/
theorem cumulativeSumMatrix_invertible (N : ℕ) :
    IsUnit (Matrix.det (fun r s : Fin N => if s ≤ r then (1 : ℚ) else 0)) := by
  rw [(cumulativeSumMatrix_structure N).2]
  exact isUnit_one

end MathlibPlus.LinearAlgebra.Claim17235
