import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

namespace MathlibPlus.GraphTheory.SelfInverseFiberSwap

/--
Claims 29782 and 41261: in the self-inverse base case, the identity-base
shear on `C₂ × C₂` has trivial normalized relative derivatives but does not
fix the singleton connection set on the nonidentity fibre.
-/
theorem selfInverseActiveBasePointBreaksSetFixing :
    ∃ f : (ZMod 2 × ZMod 2) ≃+ (ZMod 2 × ZMod 2),
      (∀ v h : ZMod 2, f (v, h) = (v + h, h)) ∧
      f.toEquiv 0 = 0 ∧
      (∀ k x : ZMod 2 × ZMod 2,
        f.toEquiv.symm (f.toEquiv (x + k) - f.toEquiv k) = x) ∧
      ∃ S : Set (ZMod 2 × ZMod 2),
          S = {((0 : ZMod 2), 1)} ∧
          f '' S = {((1 : ZMod 2), 1)} ∧
          (∀ x ∈ S, -x ∈ S) ∧
          (∀ x ∈ f '' S, -x ∈ f '' S) ∧
          f '' S ≠ S ∧
          (1 : ZMod 2) ≠ 0 ∧ -(1 : ZMod 2) = 1 := by
  let raw : (ZMod 2 × ZMod 2) → (ZMod 2 × ZMod 2) :=
    fun p => (p.1 + p.2, p.2)
  have htwo : (2 : ZMod 2) = 0 := by decide
  have hneg : -(1 : ZMod 2) = 1 := by decide
  have hchar (h : ZMod 2) : h + h = 0 := by
    calc
      h + h = (2 : ZMod 2) * h := (two_mul h).symm
      _ = 0 := by rw [htwo, zero_mul]
  have hinv : Function.Involutive raw := by
    intro p
    rcases p with ⟨v, h⟩
    dsimp [raw]
    apply Prod.ext
    · rw [add_assoc, hchar, add_zero]
    · rfl
  have hadd : ∀ p q, raw (p + q) = raw p + raw q := by
    intro p q
    rcases p with ⟨v, h⟩
    rcases q with ⟨w, k⟩
    dsimp [raw]
    apply Prod.ext
    · abel
    · rfl
  have hbij : Function.Bijective raw := by
    constructor
    · intro p q hpq
      have h := congrArg raw hpq
      rw [hinv p, hinv q] at h
      exact h
    · intro p
      exact ⟨raw p, hinv p⟩
  let f : (ZMod 2 × ZMod 2) ≃+ (ZMod 2 × ZMod 2) :=
    AddEquiv.mk (Equiv.ofBijective raw hbij) hadd
  have hformula (v h : ZMod 2) : f (v, h) = (v + h, h) := by
    rfl
  have hf : f.toEquiv 0 = 0 := by
    change raw 0 = 0
    rfl
  have hderiv : ∀ k x : ZMod 2 × ZMod 2,
      f.toEquiv.symm (f.toEquiv (x + k) - f.toEquiv k) = x := by
    intro k x
    have hmap : f.toEquiv (x + k) - f.toEquiv k = f.toEquiv x := by
      change f (x + k) - f k = f x
      rw [f.map_add]
      exact add_sub_cancel_right _ _
    rw [hmap]
    exact f.toEquiv.symm_apply_apply x
  refine ⟨f, hformula, hf, hderiv, {((0 : ZMod 2), 1)}, ?_⟩
  have himage : f '' ({((0 : ZMod 2), 1)} : Set (ZMod 2 × ZMod 2)) =
      {((1 : ZMod 2), 1)} := by
    ext x
    simp [hformula]
  have hS : ∀ x ∈ ({((0 : ZMod 2), 1)} : Set (ZMod 2 × ZMod 2)), -x ∈
      ({((0 : ZMod 2), 1)} : Set (ZMod 2 × ZMod 2)) := by
    intro x hx
    have hx' : x = ((0 : ZMod 2), 1) := by simpa using hx
    subst x
    simp [hneg]
  have hT : ∀ x ∈ f '' ({((0 : ZMod 2), 1)} : Set (ZMod 2 × ZMod 2)), -x ∈
      f '' ({((0 : ZMod 2), 1)} : Set (ZMod 2 × ZMod 2)) := by
    rw [himage]
    intro x hx
    have hx' : x = ((1 : ZMod 2), 1) := by simpa using hx
    subst x
    simp [hneg]
  refine ⟨rfl, himage, hS, hT, ?_, ?_, ?_⟩
  · rw [himage]
    intro heq
    have hmem : ((1 : ZMod 2), 1) ∈ ({((0 : ZMod 2), 1)} : Set (ZMod 2 × ZMod 2)) := by
      rw [← heq]
      simp
    simpa using hmem
  · decide
  · exact hneg

end MathlibPlus.GraphTheory.SelfInverseFiberSwap
