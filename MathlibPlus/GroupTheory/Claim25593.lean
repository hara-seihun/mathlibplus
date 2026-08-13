import MathlibPlus.Basic
import Mathlib.GroupTheory.SpecificGroups.Quaternion

namespace MathlibPlus.GroupTheory.Claim25593

private lemma add15_twice (i : ZMod 30) : i + 15 + 15 = i := by
  have h : (15 : ZMod 30) + 15 = 0 := by decide
  rw [add_assoc, h, add_zero]

private lemma fifteen_ne_zero : (15 : ZMod 30) ≠ 0 := by decide

private def kernelAut : QuaternionGroup 15 ≃* QuaternionGroup 15 where
  toFun
    | QuaternionGroup.a i => QuaternionGroup.a i
    | QuaternionGroup.xa i => QuaternionGroup.xa (i + 15)
  invFun
    | QuaternionGroup.a i => QuaternionGroup.a i
    | QuaternionGroup.xa i => QuaternionGroup.xa (i + 15)
  left_inv := by
    rintro (i | i)
    · rfl
    · change QuaternionGroup.xa (i + 15 + 15) = QuaternionGroup.xa i
      congr 1
      exact add15_twice i
  right_inv := by
    rintro (i | i)
    · rfl
    · change QuaternionGroup.xa (i + 15 + 15) = QuaternionGroup.xa i
      congr 1
      exact add15_twice i
  map_mul' := by
    rintro (i | i) (j | j) <;> simp [add_assoc, sub_eq_add_neg] <;> ring

theorem kernelAutomorphism_swaps_reflection_inverse_pairs_claim25593 :
    (∀ i : ZMod 30,
      kernelAut (QuaternionGroup.a i) = QuaternionGroup.a i ∧
      kernelAut (QuaternionGroup.xa i) = QuaternionGroup.xa (i + 15) ∧
      kernelAut (QuaternionGroup.xa (i + 15)) = QuaternionGroup.xa i) ∧
    (∀ i : ZMod 30,
      kernelAut '' ({QuaternionGroup.a i, QuaternionGroup.a (-i)} : Set (QuaternionGroup 15)) =
        {QuaternionGroup.a i, QuaternionGroup.a (-i)}) ∧
    (∀ i : ZMod 30,
      kernelAut ''
          ({QuaternionGroup.xa (n := 15) i,
            QuaternionGroup.xa (n := 15) (i + 15)} : Set (QuaternionGroup 15)) =
        {QuaternionGroup.xa (n := 15) i,
          QuaternionGroup.xa (n := 15) (i + 15)}) ∧
    (∀ i : ZMod 30,
      kernelAut (QuaternionGroup.xa i) = QuaternionGroup.xa (i + 15) ∧
      kernelAut (QuaternionGroup.xa (i + 15)) = QuaternionGroup.xa i) ∧
    kernelAut (QuaternionGroup.xa 0) ≠ QuaternionGroup.xa 0 := by
  constructor
  · intro i
    refine ⟨rfl, rfl, ?_⟩
    change QuaternionGroup.xa (n := 15) (i + 15 + 15) =
      QuaternionGroup.xa (n := 15) i
    congr 1
    exact add15_twice i
  constructor
  · intro i
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy ⊢
      rcases hy with rfl | rfl
      · simp [kernelAut]
      · change QuaternionGroup.a (-(i)) ∈
          ({QuaternionGroup.a i, QuaternionGroup.a (-i)} : Set (QuaternionGroup 15))
        simp
    · intro hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
      rcases hx with rfl | rfl
      · exact ⟨QuaternionGroup.a i, by simp, by simp [kernelAut]⟩
      · exact ⟨QuaternionGroup.a (-i), by simp, by simp [kernelAut]⟩
  constructor
  · intro i
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy ⊢
      rcases hy with rfl | rfl
      · simp [kernelAut]
      · change QuaternionGroup.xa (n := 15) (i + 15 + 15) ∈
          ({QuaternionGroup.xa (n := 15) i,
            QuaternionGroup.xa (n := 15) (i + 15)} : Set (QuaternionGroup 15))
        rw [add15_twice]
        simp
    · intro hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
      rcases hx with rfl | rfl
      · exact ⟨QuaternionGroup.xa (n := 15) (i + 15), by simp, by
          change QuaternionGroup.xa (n := 15) (i + 15 + 15) = _
          rw [add15_twice]⟩
      · exact ⟨QuaternionGroup.xa (n := 15) i, by simp, by simp [kernelAut]⟩
  constructor
  · intro i
    refine ⟨rfl, ?_⟩
    change QuaternionGroup.xa (n := 15) (i + 15 + 15) =
      QuaternionGroup.xa (n := 15) i
    congr 1
    exact add15_twice i
  · change QuaternionGroup.xa (n := 15) (0 + 15) ≠ QuaternionGroup.xa (n := 15) 0
    intro h
    injection h with h
    exact fifteen_ne_zero h

end MathlibPlus.GroupTheory.Claim25593
