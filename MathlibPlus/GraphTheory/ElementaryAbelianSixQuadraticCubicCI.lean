import Mathlib

namespace MathlibPlus.GraphTheory

private abbrev elementaryAbelianSixV := Fin 6 → ZMod 2

private def elementaryAbelianSixQuadratic (x : elementaryAbelianSixV) : ZMod 2 :=
  x 0 * x 1 + x 2 * x 3 + x 4 * x 5

private def elementaryAbelianSixCubic (x : elementaryAbelianSixV) : ZMod 2 :=
  x 0 * x 1 * x 2 + x 0 * x 3 + x 1 * x 4 + x 2 * x 5

private def elementaryAbelianSixPermutation (x : elementaryAbelianSixV) :
    elementaryAbelianSixV := fun i =>
  match i with
  | 0 => x 1 + x 2 + x 5
  | 1 => x 0 + x 3
  | 2 => x 0 + x 3 + x 5
  | 3 => x 3 + x 5 + x 0 * x 5 + x 3 * x 5
  | 4 =>
      x 1 + x 0 * x 1 + x 0 * x 2 + x 3 + x 1 * x 3 + x 2 * x 3 +
        x 4 + x 5 + x 0 * x 5 + x 1 * x 5 + x 2 * x 5 + x 3 * x 5
  | 5 =>
      x 1 + x 0 * x 1 + x 2 + x 0 * x 2 + x 3 + x 1 * x 3 + x 2 * x 3 +
        x 4 + x 5 + x 0 * x 5 + x 3 * x 5

private theorem elementaryAbelianSixPermutation_bijective :
    Function.Bijective elementaryAbelianSixPermutation := by
  native_decide

private noncomputable def elementaryAbelianSixEquiv :
    elementaryAbelianSixV ≃ elementaryAbelianSixV :=
  Equiv.ofBijective elementaryAbelianSixPermutation
    elementaryAbelianSixPermutation_bijective

private def elementaryAbelianSixQuadraticSupport : Set elementaryAbelianSixV :=
  {x | elementaryAbelianSixQuadratic x = 1}

private def elementaryAbelianSixCubicSupport : Set elementaryAbelianSixV :=
  {x | elementaryAbelianSixCubic x = 1}

private def elementaryAbelianSixThirdDifference (f : elementaryAbelianSixV → ZMod 2)
    (a b c x : elementaryAbelianSixV) : ZMod 2 :=
  f x + f (x + a) + f (x + b) + f (x + a + b) +
    f (x + c) + f (x + a + c) + f (x + b + c) + f (x + a + b + c)

private def elementaryAbelianSixE0 : elementaryAbelianSixV := ![1, 0, 0, 0, 0, 0]
private def elementaryAbelianSixE1 : elementaryAbelianSixV := ![0, 1, 0, 0, 0, 0]
private def elementaryAbelianSixE2 : elementaryAbelianSixV := ![0, 0, 1, 0, 0, 0]

private theorem elementaryAbelianSixQuadratic_thirdDifference
    (a b c x : elementaryAbelianSixV) :
    elementaryAbelianSixThirdDifference elementaryAbelianSixQuadratic a b c x = 0 := by
  simp [elementaryAbelianSixThirdDifference, elementaryAbelianSixQuadratic,
    Pi.add_apply]
  ring_nf
  have h2 : (2 : ZMod 2) = 0 := by decide
  have h4 : (4 : ZMod 2) = 0 := by decide
  have h8 : (8 : ZMod 2) = 0 := by decide
  simp [h2, h4, h8]

private theorem elementaryAbelianSixCubic_thirdDifference :
    elementaryAbelianSixThirdDifference elementaryAbelianSixCubic
      elementaryAbelianSixE0 elementaryAbelianSixE1 elementaryAbelianSixE2 0 = 1 := by
  native_decide

private lemma elementaryAbelianSix_zmod2_cases (u : ZMod 2) : u = 0 ∨ u = 1 := by
  have hlt : u.val < 2 := ZMod.val_lt u
  have hv : u.val = 0 ∨ u.val = 1 := by
    omega
  rcases hv with hv | hv
  · left
    apply ZMod.val_injective 2
    rw [hv, ZMod.val_zero]
  · right
    apply ZMod.val_injective 2
    rw [hv, ZMod.val_one]

private lemma elementaryAbelianSix_image_mem_iff (α : elementaryAbelianSixV ≃+
    elementaryAbelianSixV) (z : elementaryAbelianSixV) :
    z ∈ α '' elementaryAbelianSixQuadraticSupport ↔
      α.symm z ∈ elementaryAbelianSixQuadraticSupport := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa using hx
  · intro hz
    exact ⟨α.symm z, hz, by simp⟩

private lemma elementaryAbelianSix_support_value_transfer
    (α : elementaryAbelianSixV ≃+ elementaryAbelianSixV)
    (h : α '' elementaryAbelianSixQuadraticSupport =
      elementaryAbelianSixCubicSupport) (z : elementaryAbelianSixV) :
    elementaryAbelianSixQuadratic (α.symm z) = elementaryAbelianSixCubic z := by
  have hm' : α.symm z ∈ elementaryAbelianSixQuadraticSupport ↔
      z ∈ elementaryAbelianSixCubicSupport := by
    rw [← elementaryAbelianSix_image_mem_iff α z, h]
  have hm : elementaryAbelianSixQuadratic (α.symm z) = 1 ↔
      elementaryAbelianSixCubic z = 1 := by
    simpa [elementaryAbelianSixQuadraticSupport,
      elementaryAbelianSixCubicSupport] using hm'
  rcases elementaryAbelianSix_zmod2_cases
      (elementaryAbelianSixQuadratic (α.symm z)) with hq | hq <;>
    rcases elementaryAbelianSix_zmod2_cases
      (elementaryAbelianSixCubic z) with hc | hc <;>
    simp_all [hm]

private lemma elementaryAbelianSix_thirdDifference_comp_addEquiv
    (f : elementaryAbelianSixV → ZMod 2) (α : elementaryAbelianSixV ≃+
      elementaryAbelianSixV) (a b c x : elementaryAbelianSixV) :
    elementaryAbelianSixThirdDifference (fun z => f (α z)) a b c x =
      elementaryAbelianSixThirdDifference f (α a) (α b) (α c) (α x) := by
  simp [elementaryAbelianSixThirdDifference, map_add]

private theorem elementaryAbelianSix_no_additive_transporter :
    ¬ ∃ α : elementaryAbelianSixV ≃+ elementaryAbelianSixV,
      α '' elementaryAbelianSixQuadraticSupport =
        elementaryAbelianSixCubicSupport := by
  rintro ⟨α, hα⟩
  have hfun : ∀ w : elementaryAbelianSixV,
      elementaryAbelianSixCubic (α w) = elementaryAbelianSixQuadratic w := by
    intro w
    have hz := elementaryAbelianSix_support_value_transfer α hα (α w)
    simpa using hz.symm
  have hzero : α.symm (0 : elementaryAbelianSixV) = 0 := by simp
  have hqthird := elementaryAbelianSixQuadratic_thirdDifference
    (α.symm elementaryAbelianSixE0) (α.symm elementaryAbelianSixE1)
    (α.symm elementaryAbelianSixE2) (α.symm 0)
  have hcomp : (fun w : elementaryAbelianSixV => elementaryAbelianSixCubic (α w)) =
      elementaryAbelianSixQuadratic := funext hfun
  rw [← hcomp] at hqthird
  rw [elementaryAbelianSix_thirdDifference_comp_addEquiv] at hqthird
  have hbad : elementaryAbelianSixThirdDifference elementaryAbelianSixCubic
      elementaryAbelianSixE0 elementaryAbelianSixE1 elementaryAbelianSixE2 0 = 0 := by
    simpa [hzero] using hqthird
  rw [elementaryAbelianSixCubic_thirdDifference] at hbad
  norm_num at hbad

end MathlibPlus.GraphTheory

namespace MathlibPlus.Open.GraphTheory

/--
An explicit ordinary-CI defect on the elementary abelian group `F₂⁶`.
The two Boolean support functions have 28 points each and are related by a
normalized nonlinear permutation in the right-Cayley condition.  The final
conjunct records the cubic-versus-quadratic derivative obstruction to an
additive (hence linear) transporter.
-/
def elementaryAbelianSixQuadraticCubicCIDefect : Prop :=
  let V := Fin 6 → ZMod 2
  let fQ : V → ZMod 2 := fun x =>
    x 0 * x 1 + x 2 * x 3 + x 4 * x 5
  let fC : V → ZMod 2 := fun x =>
    x 0 * x 1 * x 2 + x 0 * x 3 + x 1 * x 4 + x 2 * x 5
  let SQ : Set V := {x | fQ x = 1}
  let SC : Set V := {x | fC x = 1}
  ∃ q : V ≃ V,
    q 0 = 0 ∧
    Fintype.card {x : V // fQ x = 1} = 28 ∧
    Fintype.card {x : V // fC x = 1} = 28 ∧
    (∀ x y : V, fQ (x + y) = fC (q x + q y)) ∧
    (¬ ∃ α : V ≃+ V, α '' SQ = SC)

end MathlibPlus.Open.GraphTheory

namespace MathlibPlus.GraphTheory

/-- The displayed quadratic/cubic witness closes the frontier node. -/
theorem elementaryAbelianSixQuadraticCubicCIDefect_proved :
    MathlibPlus.Open.GraphTheory.elementaryAbelianSixQuadraticCubicCIDefect := by
  change ∃ q : elementaryAbelianSixV ≃ elementaryAbelianSixV,
    q 0 = 0 ∧
    Fintype.card {x : elementaryAbelianSixV //
      elementaryAbelianSixQuadratic x = 1} = 28 ∧
    Fintype.card {x : elementaryAbelianSixV //
      elementaryAbelianSixCubic x = 1} = 28 ∧
    (∀ x y : elementaryAbelianSixV,
      elementaryAbelianSixQuadratic (x + y) =
        elementaryAbelianSixCubic (q x + q y)) ∧
    (¬ ∃ α : elementaryAbelianSixV ≃+ elementaryAbelianSixV,
      α '' elementaryAbelianSixQuadraticSupport =
        elementaryAbelianSixCubicSupport)
  refine ⟨elementaryAbelianSixEquiv, ?_, ?_, ?_, ?_, ?_⟩
  · change elementaryAbelianSixPermutation 0 = 0
    native_decide
  · native_decide
  · native_decide
  · intro x y
    change elementaryAbelianSixQuadratic (x + y) =
      elementaryAbelianSixCubic
        (elementaryAbelianSixPermutation x + elementaryAbelianSixPermutation y)
    native_decide +revert
  · exact elementaryAbelianSix_no_additive_transporter

end MathlibPlus.GraphTheory
