import Mathlib.GroupTheory.SpecificGroups.Quaternion
import Mathlib.Tactic

namespace MathlibPlus.GroupTheory

/--
Normalize a labelled directed right-Cayley relation isomorphism on the
quaternion group of order eight.  Left translation of the target map produces
an equivalence fixing the identity, carries every source fibre onto its target
fibre, and preserves the displayed right-difference incidence for every
label.  This is the normalization residue used by the open relational-CI
frontier node.
-/
theorem quaternionGroupTwo_normalizeRightCayley
    {κ : Type*} (S T : κ → Set (QuaternionGroup 2))
    (e : QuaternionGroup 2 ≃ QuaternionGroup 2)
    (h : ∀ i x y,
      x⁻¹ * y ∈ S i ↔ (e x)⁻¹ * e y ∈ T i) :
    ∃ q : QuaternionGroup 2 ≃ QuaternionGroup 2,
      q 1 = 1 ∧
      (∀ i, T i = q '' S i) ∧
      (∀ i x y,
        x⁻¹ * y ∈ S i ↔ (q x)⁻¹ * q y ∈ q '' S i) := by
  let a : QuaternionGroup 2 := e 1
  let q : QuaternionGroup 2 ≃ QuaternionGroup 2 :=
    { toFun := fun x => a⁻¹ * e x
      invFun := fun x => e.symm (a * x)
      left_inv := by
        intro x
        dsimp
        have hx : a * (a⁻¹ * e x) = e x := by group
        rw [hx, e.symm_apply_apply]
      right_inv := by
        intro x
        dsimp
        rw [e.apply_symm_apply]
        group }
  have hq_one : q 1 = 1 := by
    dsimp [q, a]
    group
  have hq_diff : ∀ x y : QuaternionGroup 2,
      (q x)⁻¹ * q y = (e x)⁻¹ * e y := by
    intro x y
    dsimp [q]
    group
  have hT : ∀ i, T i = q '' S i := by
    intro i
    apply Set.ext
    intro z
    rw [Set.mem_image_equiv]
    have hq_rhs : (e 1)⁻¹ * e (q.symm z) = z := by
      dsimp [q, a]
      rw [e.apply_symm_apply]
      group
    constructor
    · intro hz
      have hz' : (e 1)⁻¹ * e (q.symm z) ∈ T i := by
        rw [hq_rhs]
        exact hz
      have hs' := (h i 1 (q.symm z)).mpr hz'
      simpa only [inv_one, one_mul] using hs'
    · intro hz
      have hs' : 1⁻¹ * q.symm z ∈ S i := by
        simpa only [inv_one, one_mul] using hz
      have ht' := (h i 1 (q.symm z)).mp hs'
      rw [hq_rhs] at ht'
      exact ht'
  refine ⟨q, hq_one, hT, ?_⟩
  intro i x y
  rw [← hT i]
  rw [hq_diff]
  exact h i x y

end MathlibPlus.GroupTheory
