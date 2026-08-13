import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Tactic

namespace MathlibPlus.Algebra.Claim51998

/-- The defect directions of an odd map into `𝔽₃` form a subspace; the map
restricted to those directions is linear and extends to the ambient space.
This is the kernel-checkable formalization of claim 51998. -/
theorem defectKernelLinearExtension_claim51998
    {U : Type*} [AddCommGroup U] [Module (ZMod 3) U]
    [FiniteDimensional (ZMod 3) U]
    (f : U → ZMod 3)
    (hodd : ∀ x : U, f (-x) = -f x) :
    ∃ Z : Submodule (ZMod 3) U,
      (∀ a : U, a ∈ Z ↔ ∀ x : U, f (x + a) - f x - f a = 0) ∧
      ∃ φ : Z →ₗ[ZMod 3] ZMod 3,
        (∀ a : Z, φ a = f a) ∧
        ∃ ℓ : U →ₗ[ZMod 3] ZMod 3, ℓ.comp Z.subtype = φ := by
  have hzero : f 0 = 0 := by
    have h : f 0 = -f 0 := by simpa using hodd 0
    have hsum : f 0 + f 0 = 0 := by
      calc
        f 0 + f 0 = -f 0 + f 0 :=
          congrArg (fun y : ZMod 3 => y + f 0) h
        _ = 0 := by abel
    have htwo : (2 : ZMod 3) * f 0 = 0 := by
      simpa [two_mul] using hsum
    have htwo_ne : (2 : ZMod 3) ≠ 0 := by decide
    exact (mul_eq_zero.mp htwo).resolve_left htwo_ne
  have scalar_cases : ∀ c : ZMod 3, c = 0 ∨ c = 1 ∨ c = -1 := by
    intro c
    revert c
    decide
  let good : Set U := {a | ∀ x : U, f (x + a) - f x - f a = 0}
  have htrans : ∀ {a : U}, a ∈ good → ∀ x : U, f (x + a) = f x + f a := by
    intro a ha x
    have hx := ha x
    have hx' : f (x + a) - (f x + f a) = 0 := by
      convert hx using 1 <;> abel
    exact sub_eq_zero.mp hx'
  have hgood_add : ∀ {a b : U}, a ∈ good → b ∈ good → a + b ∈ good := by
    intro a b ha hb x
    have ha' := htrans ha x
    have hb' := htrans hb (x + a)
    have hab : f (a + b) = f a + f b := by
      simpa [add_comm] using htrans ha b
    have hsum : f (x + (a + b)) = f x + f (a + b) := by
      calc
        f (x + (a + b)) = f ((x + a) + b) := by rw [add_assoc]
        _ = f (x + a) + f b := hb'
        _ = (f x + f a) + f b := by rw [ha']
        _ = f x + (f a + f b) := by abel
        _ = f x + f (a + b) := by rw [hab]
    rw [hsum]
    abel
  have hgood_smul : ∀ (c : ZMod 3) {a : U}, a ∈ good → c • a ∈ good := by
    intro c a ha
    have hc := scalar_cases c
    rcases hc with rfl | rfl | rfl
    · intro x
      simp [hzero]
    · simpa using ha
    · have hneg : -a ∈ good := by
        intro x
        have hstep := htrans ha (x - a)
        have hminus : f (-a) = -f a := hodd a
        have hxa : f (x - a) = f x - f a := by
          have hx : f x = f (x - a) + f a := by
            simpa [sub_add_cancel] using hstep
          rw [eq_sub_iff_add_eq]
          exact hx.symm
        have hxa' : f (x + (-a)) = f x - f a := by
          simpa only [sub_eq_add_neg] using hxa
        rw [hxa', hminus]
        abel
      rw [neg_smul, one_smul]
      exact hneg
  let Z : Submodule (ZMod 3) U :=
    { carrier := good
      zero_mem' := by
        intro x
        simp [hzero]
      add_mem' := by
        intro a b ha hb
        exact hgood_add ha hb
      smul_mem' := by
        intro c a ha
        exact hgood_smul c ha }
  have hZ : ∀ a : U, a ∈ Z ↔ ∀ x : U, f (x + a) - f x - f a = 0 := by
    intro a
    rfl
  let φ : Z →ₗ[ZMod 3] ZMod 3 :=
    { toFun := fun a => f a
      map_add' := by
        intro a b
        have ha := htrans a.property b
        simpa [add_comm] using ha
      map_smul' := by
        intro c a
        have hc := scalar_cases c
        rcases hc with rfl | rfl | rfl
        · simp [hzero]
        · simp
        · have ha_neg : (-1 : ZMod 3) • a = -a := by
            rw [neg_smul, one_smul]
          rw [ha_neg]
          change f (-(a : U)) = (-1 : ZMod 3) • f (a : U)
          simpa [smul_eq_mul] using hodd a }
  obtain ⟨ℓ, hℓ⟩ := LinearMap.exists_extend φ
  refine ⟨Z, hZ, φ, ?_, ℓ, hℓ⟩
  intro a
  rfl

end MathlibPlus.Algebra.Claim51998
