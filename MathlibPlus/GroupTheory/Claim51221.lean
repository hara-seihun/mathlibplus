import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

namespace MathlibPlus.GroupTheory.Claim51221

private def twoCast : ℤ →+ ZMod 4 where
  toFun n := n • (2 : ZMod 4)
  map_zero' := by simp
  map_add' := by intro a b; simp only [add_zsmul]

private theorem twoCast_period : twoCast 2 = 0 := by
  change (2 : ℤ) • (2 : ZMod 4) = 0
  convert (ZMod.natCast_self 4) using 1 <;> norm_num [smul_eq_mul]

/-- The inclusion of the order-two subgroup `2 C₄` into `C₄`, with its
abstract domain identified with `C₂`. -/
def doubleHom : ZMod 2 →+ ZMod 4 :=
  ZMod.lift 2 ⟨twoCast, twoCast_period⟩

theorem doubleHom_range : AddMonoidHom.range doubleHom =
    AddSubgroup.zmultiples (2 : ZMod 4) := by
  apply le_antisymm
  · rintro y ⟨x, rfl⟩
    obtain ⟨n, rfl⟩ := ZMod.intCast_surjective x
    simp [doubleHom, ZMod.lift_coe]
    exact AddSubgroup.mem_zmultiples_iff.mpr ⟨n, rfl⟩
  · intro y hy
    obtain ⟨n, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hy
    refine ⟨(n : ZMod 2), ?_⟩
    simp [doubleHom, ZMod.lift_coe, twoCast]

theorem restriction_trivial (φ : ZMod 4 →+ ZMod 2) :
    φ.comp doubleHom = 0 := by
  apply AddMonoidHom.ext
  intro x
  obtain ⟨n, rfl⟩ := ZMod.intCast_surjective x
  rw [AddMonoidHom.comp_apply]
  change φ (doubleHom (n : ZMod 2)) = 0
  have hd : doubleHom (n : ZMod 2) = n • (2 : ZMod 4) := by
    simp [doubleHom, ZMod.lift_coe, twoCast]
  rw [hd]
  rw [map_zsmul]
  have hphi2 : φ (2 : ZMod 4) = 0 := by
    have htwo : (2 : ZMod 4) = (2 : ℤ) • (1 : ZMod 4) := by
      norm_num [smul_eq_mul]
    rw [htwo, map_zsmul]
    rw [zsmul_eq_mul]
    have hzero : ((2 : ℤ) : ZMod 2) = 0 := by decide
    rw [hzero, zero_mul]
  rw [hphi2]
  simp

theorem nontrivial_map_from_double :
    ∃ ψ : ZMod 2 →+ ZMod 2, ψ ≠ 0 := by
  refine ⟨AddMonoidHom.id (ZMod 2), ?_⟩
  intro h
  have h1 := congrArg (fun f : ZMod 2 →+ ZMod 2 => f 1) h
  simpa using h1

theorem restriction_not_surjective :
    ¬ Function.Surjective (fun φ : ZMod 4 →+ ZMod 2 => φ.comp doubleHom) := by
  intro hsurj
  obtain ⟨φ, hφ⟩ := hsurj (AddMonoidHom.id (ZMod 2))
  have hz := restriction_trivial φ
  have hid : AddMonoidHom.id (ZMod 2) = 0 := hφ.symm.trans hz
  have h1 := congrArg (fun f : ZMod 2 →+ ZMod 2 => f 1) hid
  simpa using h1

end MathlibPlus.GroupTheory.Claim51221
