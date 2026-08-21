-- UNVERIFIED (native-decide): submitted but not kernel-verified, so it is not built and MathlibPlus.lean does not import it. See unverified.txt.
import Mathlib

namespace MathlibPlus.Open.Research.R1645

abbrev F7 := ZMod 7
abbrev F3 := ZMod 3

private instance : Fact (1 < 7) := ⟨by decide⟩
private instance : Fact (1 < 3) := ⟨by decide⟩
private instance : Fact (Nat.Prime 7) := ⟨by decide⟩
private instance : Fact (Nat.Prime 3) := ⟨by decide⟩

abbrev HBase := Multiplicative F3
abbrev NBase := Multiplicative F7

private def scalar : F3 → F7 := fun i =>
  if i = 0 then 1 else if i = 1 then 2 else 4

private def scalarAddEquiv (a : F7) (ha : IsUnit a) : F7 ≃+ F7 :=
  { toFun := fun x => a * x
    invFun := fun x => a⁻¹ * x
    left_inv := by
      intro x
      change a⁻¹ * (a * x) = x
      rw [← mul_assoc]
      simp [ha.ne_zero]
    right_inv := by
      intro x
      change a * (a⁻¹ * x) = x
      rw [← mul_assoc]
      simp [ha.ne_zero]
    map_add' := by
      intro x y
      simp [mul_add] }

private def scalarAut (a : F7) (ha : IsUnit a) : MulAut NBase :=
  (scalarAddEquiv a ha).toMultiplicative

private lemma scalar_isUnit (i : F3) : IsUnit (scalar i) := by
  fin_cases i <;> native_decide

private def hAction : HBase →* MulAut NBase :=
  { toFun := fun i => scalarAut (scalar (i : F3)) (scalar_isUnit (i : F3))
    map_one' := by native_decide
    map_mul' := by
      intro i j
      fin_cases i <;> fin_cases j <;> native_decide }

abbrev H := SemidirectProduct NBase HBase hAction
abbrev W := Fin 2 → F7

private def vertical : W := fun i => if i = 1 then 1 else 0

/-- The common-flag rank-one nonlinear shear setup and its exact fiber inverse. -/
def commonFlagRankOneNonlinearShear : Prop :=
  ∀ (ℓ : W →ₗ[F7] F7) (t : W),
    ℓ ≠ 0 →
    t ≠ 0 →
    ℓ t = 0 →
    (∃ e : W ≃ₗ[F7] W,
      (∀ x, ℓ x = (e x) 0) ∧ e t = vertical) ∧
    ∀ (q : F7 → F7) (c : H → F7),
      q 0 = 0 →
      c 1 = 0 →
      let f : (W × H) → (W × H) :=
        fun p =>
          ((fun i => if i = 0 then p.1 0 else p.1 1 + c p.2 * q (p.1 0)), p.2)
      let g : (W × H) → (W × H) :=
        fun p =>
          ((fun i => if i = 0 then p.1 0 else p.1 1 - c p.2 * q (p.1 0)), p.2)
      Function.Bijective f ∧
        Function.LeftInverse g f ∧ Function.RightInverse g f

end MathlibPlus.Open.Research.R1645
