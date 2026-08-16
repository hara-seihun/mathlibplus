import Mathlib

/-!
# The characteristic-two boundary of Euler-curvature coordinates

This file formalizes the exact boundary in admitted claim 5183 (source record
D-0085).  The degree, quadratic, neighbor-transport, and leaf-graft identities
are retained over the integers.  The characteristic-two failure is recorded by
the zero determinant of the coordinate-change matrix and by an explicit
quadratic-channel non-recovery witness.
-/

namespace MathlibPlus.GraphTheory

private theorem two_choose_two_nat (n : ℕ) :
    2 * Nat.choose n 2 = n * (n - 1) := by
  rw [Nat.choose_two_right]
  simpa [Nat.mul_comm] using
    (Nat.div_mul_cancel (Nat.even_mul_pred_self n).two_dvd)

private def integerCurvature (d : ℕ) : ℤ := 2 - d

theorem characteristicTwo_degree_curvature_identity_claim5183 (d : ℕ) :
    (d : ℤ) = 2 - integerCurvature d := by
  simp [integerCurvature]

theorem characteristicTwo_quadratic_curvature_identity_claim5183 (d : ℕ) :
    2 * (Nat.choose d 2 : ℤ) =
      integerCurvature d ^ 2 - 3 * integerCurvature d + 2 := by
  have h := two_choose_two_nat d
  calc
    2 * (Nat.choose d 2 : ℤ) = ((2 * Nat.choose d 2 : ℕ) : ℤ) := by norm_num
    _ = ((d * (d - 1) : ℕ) : ℤ) := by rw [h]
    _ = (2 - (d : ℤ)) ^ 2 - 3 * (2 - (d : ℤ)) + 2 := by
      by_cases hd : d = 0
      · simp [hd]
      · have hpos : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr hd
        push_cast
        rw [Nat.cast_sub hpos]
        ring
    _ = integerCurvature d ^ 2 - 3 * integerCurvature d + 2 := by
      rfl

section Neighbor

variable {V : Type*} [Fintype V] [DecidableEq V]

private def attachmentDegree (neighbors : V → Finset V) (v : V) : ℕ :=
  (neighbors v).card

private def curvature (neighbors : V → Finset V) (v : V) : ℤ :=
  2 - attachmentDegree neighbors v

private def attachmentChannel (neighbors : V → Finset V) (v : V) : ℤ :=
  ∑ x ∈ neighbors v, ((attachmentDegree neighbors x : ℤ) - 1)

private def transportedCurvature (neighbors : V → Finset V) (v : V) : ℤ :=
  ∑ x ∈ neighbors v, curvature neighbors x

/-- The integral identity `m = d - Aχ`, with adjacency represented by the
finite neighbor sets.  No characteristic assumption is used. -/
theorem characteristicTwo_attachment_curvature_identity_claim5183
    (neighbors : V → Finset V) (v : V) :
    attachmentChannel neighbors v =
      (attachmentDegree neighbors v : ℤ) - transportedCurvature neighbors v := by
  simp only [attachmentChannel, transportedCurvature]
  simp_rw [sub_eq_add_neg]
  rw [Finset.sum_add_distrib]
  simp [attachmentDegree, curvature]
  ring

private def graftLeaf (neighbors : V → Finset V) (root : V) :
    Option V → Finset (Option V)
  | none => {some root}
  | some v =>
      (neighbors v).image some ∪ if v = root then {none} else ∅

private def extendByZero (f : V → ℤ) : Option V → ℤ
  | none => 0
  | some v => f v

private def newLeafBasis : Option V → ℤ
  | none => 1
  | some _ => 0

private def oldVertexBasis (root : V) : Option V → ℤ
  | none => 0
  | some v => if v = root then 1 else 0

/-- The integral leaf-graft dipole insertion
`χ_(C+_v ell) = χ_C + e_ell - e_v`. -/
theorem characteristicTwo_graft_curvature_dipole_claim5183
    (neighbors : V → Finset V) (root : V) :
    curvature (graftLeaf neighbors root) =
      extendByZero (curvature neighbors) + newLeafBasis - oldVertexBasis root := by
  funext w
  cases w with
  | none =>
      simp [curvature, attachmentDegree, graftLeaf, extendByZero,
        newLeafBasis, oldVertexBasis]
  | some v =>
      by_cases h : v = root
      · subst v
        simp [curvature, attachmentDegree, graftLeaf, extendByZero,
          newLeafBasis, oldVertexBasis,
          Finset.card_image_of_injective _ (Option.some_injective V)]
        push_cast
        ring
      · simp [curvature, attachmentDegree, graftLeaf, extendByZero,
          newLeafBasis, oldVertexBasis, h,
          Finset.card_image_of_injective _ (Option.some_injective V)]

end Neighbor

private def characteristicTwoCoordinateMatrix (R : Type*) [Ring R] :
    Matrix (Fin 4) (Fin 4) R :=
  !![1, 0, 0, 0;
     2, -1, 0, 0;
     4, -3, 2, 0;
     0, 1, 0, -1]

theorem characteristicTwo_coordinate_failure_claim5183 :
    Matrix.det (characteristicTwoCoordinateMatrix (ZMod 2)) = 0 := by
  have htri :
      (characteristicTwoCoordinateMatrix (ZMod 2)).IsLowerTriangular := by
    intro i j hij
    change i < j at hij
    fin_cases i <;> fin_cases j <;>
      simp_all [characteristicTwoCoordinateMatrix]
  rw [Matrix.det_of_isLowerTriangular
    (characteristicTwoCoordinateMatrix (ZMod 2)) htri]
  norm_num [characteristicTwoCoordinateMatrix, Fin.prod_univ_succ] <;> decide

/-- In characteristic two, the square of the curvature coordinate does not
recover the quadratic degree channel, already at degree one. -/
theorem characteristicTwo_quadratic_nonrecovery_claim5183 :
    (Nat.choose 1 2 : ZMod 2) ≠ (2 - (1 : ZMod 2)) ^ 2 := by
  norm_num [Nat.choose]

/-- The integral identities and the characteristic-two failure in one exact
claim-level conjunction. -/
theorem characteristicTwoBoundary_claim5183 :
    (∀ d : ℕ, (d : ℤ) = 2 - integerCurvature d) ∧
      (∀ d : ℕ, 2 * (Nat.choose d 2 : ℤ) =
        integerCurvature d ^ 2 - 3 * integerCurvature d + 2) ∧
      Matrix.det (characteristicTwoCoordinateMatrix (ZMod 2)) = 0 ∧
      (Nat.choose 1 2 : ZMod 2) ≠ (2 - (1 : ZMod 2)) ^ 2 := by
  exact ⟨characteristicTwo_degree_curvature_identity_claim5183,
    characteristicTwo_quadratic_curvature_identity_claim5183,
    characteristicTwo_coordinate_failure_claim5183,
    characteristicTwo_quadratic_nonrecovery_claim5183⟩

end MathlibPlus.GraphTheory
