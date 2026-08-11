import Mathlib

namespace MathlibPlus.Algebra

/--
Claim 27695: a fixed-point-free order-three additive endomorphism has a
unit difference from the identity and its three-term geometric sum vanishes.
The source's `theta - 1` is represented in the endomorphism ring
`AddMonoid.End A`.
-/
theorem fixedPointFreeOrderThreeOperator
    {A : Type*} [AddCommGroup A] [Fintype A]
    (θ : AddMonoid.End A)
    (hθ : θ ^ 3 = (1 : AddMonoid.End A))
    (hfree : ∀ x : A, θ x = x → x = 0) :
    IsUnit (θ - 1) ∧ (1 + θ + θ ^ 2 : AddMonoid.End A) = 0 := by
  let f : AddMonoid.End A := 1 - θ
  have hf_inj : Function.Injective f := by
    intro x y hxy
    have hz : f (x - y) = 0 := by
      calc
        f (x - y) = f x - f y := map_sub f x y
        _ = 0 := by rw [hxy, sub_self]
    have hz' : (x - y) - θ (x - y) = 0 := by
      dsimp [f] at hz
      change (x - y) - θ (x - y) = 0 at hz
      exact hz
    have hfix : θ (x - y) = x - y := (sub_eq_zero.mp hz').symm
    exact sub_eq_zero.mp (hfree (x - y) hfix)
  have hf_surj : Function.Surjective f :=
    (Finite.injective_iff_surjective).mp hf_inj
  let e : A ≃+ A := AddEquiv.ofBijective f ⟨hf_inj, hf_surj⟩
  have hunit : IsUnit f := by
    refine ⟨Units.mk f e.symm.toAddMonoidHom ?_ ?_, ?_⟩
    · apply AddMonoidHom.ext
      intro x
      change f (e.symm x) = x
      exact e.apply_symm_apply x
    · apply AddMonoidHom.ext
      intro x
      change e.symm (f x) = x
      exact e.symm_apply_apply x
    · rfl
  have hprod : f * (1 + θ + θ ^ 2) = 0 := by
    dsimp [f]
    calc
      (1 - θ) * (1 + θ + θ ^ 2) = 1 - θ ^ 3 := by noncomm_ring
      _ = 0 := by rw [hθ]; simp
  have hunit' : IsUnit (θ - 1) := by
    rw [show θ - 1 = -(1 - θ) by noncomm_ring]
    exact hunit.neg
  constructor
  · exact hunit'
  · apply hunit.mul_left_cancel
    simpa using hprod

end MathlibPlus.Algebra
