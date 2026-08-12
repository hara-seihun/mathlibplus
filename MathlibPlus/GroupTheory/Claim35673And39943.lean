import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Algebra.Module.Equiv.Basic
import Mathlib.Tactic

namespace MathlibPlus.GroupTheory

/-- Claim R-2766: the C₂ × C₃³ automorphism coordinate form and its C₄-lift. -/
theorem claim35673_groupAutomorphismCoordinateForm
    (β : (ZMod 2 × (Fin 3 → ZMod 3)) ≃+
      (ZMod 2 × (Fin 3 → ZMod 3))) :
    (∀ x : ZMod 2 × (Fin 3 → ZMod 3), x ≠ 0 → 2 • x = 0 →
        x = ((1 : ZMod 2), 0)) ∧
      β ((1 : ZMod 2), 0) = ((1 : ZMod 2), 0) ∧
      ∃ B : (Fin 3 → ZMod 3) ≃ₗ[ZMod 3] (Fin 3 → ZMod 3),
        (∀ ε : ZMod 2, ∀ v : Fin 3 → ZMod 3,
          β (ε, v) = (ε, B v)) ∧
          ∃ βtilde : (ZMod 4 × (Fin 3 → ZMod 3)) ≃+
              (ZMod 4 × (Fin 3 → ZMod 3)),
            ∀ a : ZMod 4, ∀ v : Fin 3 → ZMod 3,
              βtilde (a, v) = (a, B v) := by
  have zmod2_cases : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by
    intro x
    have hval : x.val < 2 := ZMod.val_lt x
    have hx' : x = (x.val : ZMod 2) := (ZMod.natCast_zmod_val x).symm
    rw [hx']
    interval_cases h : x.val <;> simp_all
  have zmod3_cases : ∀ x : ZMod 3, x = 0 ∨ x = 1 ∨ x = 2 := by
    intro x
    have hval : x.val < 3 := ZMod.val_lt x
    have hx' : x = (x.val : ZMod 3) := (ZMod.natCast_zmod_val x).symm
    rw [hx']
    interval_cases h : x.val <;> simp_all
  have zmod2_of_three_nsmul_zero : ∀ x : ZMod 2, 3 • x = 0 → x = 0 := by
    intro x hx
    have hval : x.val < 2 := ZMod.val_lt x
    have hx' : x = (x.val : ZMod 2) := (ZMod.natCast_zmod_val x).symm
    rw [hx'] at hx ⊢
    interval_cases h : x.val
    · rfl
    · exfalso
      exact (by native_decide : (3 : ZMod 2) ≠ 0) hx
  have zmod3_of_two_nsmul_zero : ∀ x : ZMod 3, 2 • x = 0 → x = 0 := by
    intro x hx
    have hval : x.val < 3 := ZMod.val_lt x
    have hx' : x = (x.val : ZMod 3) := (ZMod.natCast_zmod_val x).symm
    rw [hx'] at hx ⊢
    interval_cases h : x.val
    · rfl
    · exfalso
      exact (by native_decide : (2 : ZMod 3) ≠ 0) hx
    · exfalso
      exact (by native_decide : (4 : ZMod 3) ≠ 0) hx
  have V_of_two_nsmul_zero : ∀ x : Fin 3 → ZMod 3, 2 • x = 0 → x = 0 := by
    intro x hx
    funext i
    apply zmod3_of_two_nsmul_zero (x i)
    have hxi := congrFun hx i
    simpa [Pi.smul_apply] using hxi
  have three_smul_V : ∀ v : Fin 3 → ZMod 3, 3 • v = 0 := by
    intro v
    funext i
    rw [Pi.smul_apply, nsmul_eq_mul, ZMod.natCast_self]
    simp
  have three_smul_H : ∀ v : Fin 3 → ZMod 3,
      3 • ((0 : ZMod 2), v) = ((0 : ZMod 2), (0 : Fin 3 → ZMod 3)) := by
    intro v
    apply Prod.ext
    · change 3 • (0 : ZMod 2) = 0
      simp [nsmul_eq_mul]
    · exact three_smul_V v
  have two_smul_H_special :
      2 • ((1 : ZMod 2), (0 : Fin 3 → ZMod 3)) =
        ((0 : ZMod 2), (0 : Fin 3 → ZMod 3)) := by
    apply Prod.ext
    · change 2 • (1 : ZMod 2) = 0
      rw [nsmul_eq_mul, ZMod.natCast_self]
      simp
    · change 2 • (0 : Fin 3 → ZMod 3) = 0
      simp
  have hUnique : ∀ x : ZMod 2 × (Fin 3 → ZMod 3), x ≠ 0 → 2 • x = 0 →
      x = ((1 : ZMod 2), 0) := by
    intro x hxne hxorder
    have hsecond_x : x.2 = 0 := by
      apply V_of_two_nsmul_zero
      have hxs := congrArg Prod.snd hxorder
      simpa only [Prod.smul_snd, Prod.snd_zero] using hxs
    rcases zmod2_cases x.1 with hx0 | hx1
    · exfalso
      apply hxne
      exact Prod.ext hx0 hsecond_x
    · exact Prod.ext hx1 hsecond_x
  have hzero : β (0, 0) = (0, 0) := by
    change β (0 : ZMod 2 × (Fin 3 → ZMod 3)) = 0
    exact β.map_zero
  have hfirst : ∀ v : Fin 3 → ZMod 3, (β (0, v)).1 = 0 := by
    intro v
    apply zmod2_of_three_nsmul_zero
    have hb := congrArg (β : (ZMod 2 × (Fin 3 → ZMod 3)) →
      (ZMod 2 × (Fin 3 → ZMod 3))) (three_smul_H v)
    have hbf := congrArg Prod.fst hb
    rw [hzero] at hbf
    simpa only [Prod.smul_fst, map_nsmul] using hbf
  have hsecond : (β ((1 : ZMod 2), 0)).2 = 0 := by
    apply V_of_two_nsmul_zero
    have hb := congrArg (β : (ZMod 2 × (Fin 3 → ZMod 3)) →
      (ZMod 2 × (Fin 3 → ZMod 3))) two_smul_H_special
    have hbs := congrArg Prod.snd hb
    rw [hzero] at hbs
    simpa only [Prod.smul_snd, map_nsmul] using hbs
  have hfix : β ((1 : ZMod 2), 0) = ((1 : ZMod 2), 0) := by
    have hne : (β ((1 : ZMod 2), 0)).1 ≠ 0 := by
      intro hz
      have heq : β ((1 : ZMod 2), 0) = (0, 0) := by
        apply Prod.ext
        · exact hz
        · exact hsecond
      have hbeq : β ((1 : ZMod 2), 0) = β (0, 0) := heq.trans hzero.symm
      have hsrc : ((1 : ZMod 2), (0 : Fin 3 → ZMod 3)) =
          ((0 : ZMod 2), (0 : Fin 3 → ZMod 3)) := β.injective hbeq
      have hne_src : ((1 : ZMod 2), (0 : Fin 3 → ZMod 3)) ≠
          ((0 : ZMod 2), (0 : Fin 3 → ZMod 3)) := by
        intro h
        have := congrArg Prod.fst h
        simpa using this
      exact hne_src hsrc
    have hfirst_one : (β ((1 : ZMod 2), 0)).1 = 1 :=
      (zmod2_cases _).resolve_left hne
    exact Prod.ext hfirst_one hsecond
  let b : (Fin 3 → ZMod 3) →ₗ[ZMod 3] (Fin 3 → ZMod 3) :=
    { toFun := fun v => (β (0, v)).2
      map_add' := by
        intro v w
        have hβ := β.map_add ((0 : ZMod 2), v) ((0 : ZMod 2), w)
        have harg : ((0 : ZMod 2), v) + ((0 : ZMod 2), w) =
            ((0 : ZMod 2), v + w) := by
          ext <;> simp
        rw [harg] at hβ
        have hβs := congrArg Prod.snd hβ
        simpa only [Prod.snd_add] using hβs
      map_smul' := by
        intro c v
        rcases zmod3_cases c with rfl | rfl | rfl
        · simpa using congrArg Prod.snd hzero
        · simp
        · have hβ := β.map_add ((0 : ZMod 2), v) ((0 : ZMod 2), v)
          have harg : ((0 : ZMod 2), v) + ((0 : ZMod 2), v) =
              ((0 : ZMod 2), v + v) := by
            ext <;> simp
          rw [harg] at hβ
          have hβs := congrArg Prod.snd hβ
          rw [show (2 : ZMod 3) = 1 + 1 by native_decide, add_smul]
          simpa [add_smul, one_smul, Prod.snd_add] using hβs }
  have hb_inj : Function.Injective b := by
    intro v w hvw
    have hβ : β (0, v) = β (0, w) := by
      apply Prod.ext
      · exact (hfirst v).trans (hfirst w).symm
      · exact hvw
    have hpair : ((0 : ZMod 2), v) = ((0 : ZMod 2), w) := by
      exact β.injective hβ
    exact congrArg Prod.snd hpair
  have hb_surj : Function.Surjective b :=
    (Finite.injective_iff_surjective.mp hb_inj)
  let B : (Fin 3 → ZMod 3) ≃ₗ[ZMod 3] (Fin 3 → ZMod 3) :=
    LinearEquiv.ofBijective b ⟨hb_inj, hb_surj⟩
  have hB_apply (v : Fin 3 → ZMod 3) : B v = b v := by
    exact LinearEquiv.ofBijective_apply b v
  have hcoord : ∀ ε : ZMod 2, ∀ v : Fin 3 → ZMod 3,
      β (ε, v) = (ε, B v) := by
    intro ε v
    rcases zmod2_cases ε with rfl | rfl
    · apply Prod.ext
      · exact hfirst v
      · change (β ((0 : ZMod 2), v)).2 = B v
        exact (hB_apply v).symm
    · have hdecomp : ((1 : ZMod 2), v) =
          ((1 : ZMod 2), (0 : Fin 3 → ZMod 3)) + (0, v) := by
        ext <;> simp
      rw [hdecomp, β.map_add, hfix]
      apply Prod.ext
      · simp [hfirst]
      · have hB_apply' : (β ((0 : ZMod 2), v)).2 = B v := by
          change b v = B v
          exact (hB_apply v).symm
        simpa only [Prod.snd_add, zero_add] using hB_apply'
  refine ⟨hUnique, hfix, B, hcoord, ?_⟩
  let βtilde : (ZMod 4 × (Fin 3 → ZMod 3)) ≃+
      (ZMod 4 × (Fin 3 → ZMod 3)) :=
    AddEquiv.prodCongr (AddEquiv.refl (ZMod 4)) B.toAddEquiv
  refine ⟨βtilde, ?_⟩
  intro a v
  rfl

/-- Claim R-1648: the inverse atoms of C₂³ × C₃².  The subtype `A` is the
nonidentity part, and `Finset.univ.image atom` is the set of inversion orbits. -/
theorem claim39943_inverseAtomDecomposition :
    let G := (Fin 3 → ZMod 2) × (Fin 2 → ZMod 3)
    let A := {x : G // x ≠ 0}
    let inv : A → A := fun x =>
      ⟨-x.1, by simpa using neg_ne_zero.mpr x.2⟩
    let atom : A → Finset A := fun x => {x, inv x}
    let atoms : Finset (Finset A) := Finset.univ.image atom
    Fintype.card G = 72 ∧
      Fintype.card A = 71 ∧
      (∀ s ∈ atoms, s.card = 1 ∨ s.card = 2) ∧
      (atoms.filter (fun s => s.card = 1)).card = 7 ∧
      (atoms.filter (fun s => s.card = 2)).card = 32 := by
  native_decide

end MathlibPlus.GroupTheory
