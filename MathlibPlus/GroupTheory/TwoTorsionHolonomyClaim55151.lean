import Mathlib

namespace MathlibPlus.GroupTheory

/-- Claim 55151: after quotienting the chief-section lift difference by base
translations, the inclusion `C₂ = ⟨g²⟩ < C₄ = ⟨g⟩` has a nonzero residual
`C₂`-valued class outside the image of every global character.  The statement
records the algebraic obstruction and does not assert that it is realized by a
graph defect. -/
theorem twoTorsionHolonomyDefect_claim55151 :
    ∃ ι : ZMod 2 →+ ZMod 4,
      ι (1 : ZMod 2) = 2 ∧
      (∃ e : (ZMod 2 →+ ZMod 2) ≃+ ZMod 2,
        e.toFun = (fun f => f (1 : ZMod 2))) ∧
      (∀ φ : ZMod 4 →+ ZMod 2, φ.comp ι = 0) ∧
      (¬ Function.Surjective (fun φ : ZMod 4 →+ ZMod 2 => φ.comp ι)) ∧
      (∃ ψ : ZMod 2 →+ ZMod 2,
        ψ (1 : ZMod 2) ≠ 0 ∧
          ∀ φ : ZMod 4 →+ ZMod 2, φ.comp ι ≠ ψ) := by
  let f : ℤ →+ ZMod 4 :=
    (AddMonoidHom.smul (2 : ZMod 4)).comp (Int.castAddHom (ZMod 4))
  have hf : f (2 : ℤ) = 0 := by
    change (2 : ZMod 4) * (2 : ZMod 4) = 0
    calc
      (2 : ZMod 4) * (2 : ZMod 4) = (4 : ZMod 4) := by ring
      _ = 0 := ZMod.natCast_self 4
  let ι : ZMod 2 →+ ZMod 4 := ZMod.lift 2 ⟨f, hf⟩
  have hi : ι (1 : ZMod 2) = 2 := by
    change (ZMod.lift 2 ⟨f, hf⟩) ((1 : ℤ) : ZMod 2) = 2
    rw [ZMod.lift_coe]
    change (2 : ZMod 4) * (1 : ZMod 4) = 2
    norm_num
  have hphi (φ : ZMod 4 →+ ZMod 2) : φ (2 : ZMod 4) = 0 := by
    have h := φ.map_nsmul 2 (1 : ZMod 4)
    calc
      φ (2 : ZMod 4) = (2 : ℕ) • φ (1 : ZMod 4) := by
        rw [show (2 : ZMod 4) = 2 • (1 : ZMod 4) by norm_num, h]
      _ = 0 := by
        rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul]
  have heval :
      ∃ e : (ZMod 2 →+ ZMod 2) ≃+ ZMod 2,
        e.toFun = (fun f => f (1 : ZMod 2)) := by
    let eval : (ZMod 2 →+ ZMod 2) →+ ZMod 2 :=
      { toFun := fun f => f (1 : ZMod 2)
        map_zero' := by simp
        map_add' := by intro f g; simp }
    let evalInv : ZMod 2 →+ (ZMod 2 →+ ZMod 2) :=
      { toFun := fun x =>
          { toFun := fun y => y * x
            map_zero' := by simp
            map_add' := by intro y z; simp [add_mul] }
        map_zero' := by
          ext y
          simp
        map_add' := by
          intro x z
          ext y
          simp [mul_add] }
    have hleft : evalInv.comp eval = AddMonoidHom.id (ZMod 2 →+ ZMod 2) := by
      ext q y
      fin_cases y
      · change (0 : ZMod 2) * q 1 = q 0
        rw [zero_mul, q.map_zero]
      · change (1 : ZMod 2) * q 1 = q 1
        rw [one_mul]
    have hright : eval.comp evalInv = AddMonoidHom.id (ZMod 2) := by
      ext x
      simp [evalInv, eval]
    exact ⟨eval.toAddEquiv evalInv hleft hright, rfl⟩
  have hrestrict : ∀ φ : ZMod 4 →+ ZMod 2, φ.comp ι = 0 := by
    intro φ
    ext x
    fin_cases x
    · change φ (ι 0) = 0
      simp
    · change φ (ι 1) = 0
      rw [hi]
      exact hphi φ
  let ψ : ZMod 2 →+ ZMod 2 := AddMonoidHom.id (ZMod 2)
  have hnotSurj :
      ¬ Function.Surjective (fun φ : ZMod 4 →+ ZMod 2 => φ.comp ι) := by
    intro hsurj
    obtain ⟨φ, hφ⟩ := hsurj ψ
    exact (show φ.comp ι ≠ ψ from by
      intro heq
      have heval_at_one := congrArg (fun q : ZMod 2 →+ ZMod 2 => q 1) heq
      have hzero : φ (2 : ZMod 4) = 0 := hphi φ
      have hone : φ (2 : ZMod 4) = (1 : ZMod 2) := by
        simpa [hi, ψ] using heval_at_one
      exact zero_ne_one (hzero.symm.trans hone)) hφ
  refine ⟨ι, hi, heval, hrestrict, hnotSurj, ?_⟩
  
  refine ⟨ψ, ?_, ?_⟩
  · change (1 : ZMod 2) ≠ 0
    norm_num
  · intro φ heq
    have heval_at_one := congrArg (fun q : ZMod 2 →+ ZMod 2 => q 1) heq
    have : φ (2 : ZMod 4) = (1 : ZMod 2) := by
      simpa [hi, ψ] using heval_at_one
    exact zero_ne_one ((hphi φ).symm.trans this)

end MathlibPlus.GroupTheory
