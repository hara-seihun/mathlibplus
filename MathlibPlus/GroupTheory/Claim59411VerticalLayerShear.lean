import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Group.Equiv.TypeTags

namespace MathlibPlus.GroupTheory

theorem normalizedVerticalLayerShear_bijective_claim59411
    {p : ℕ}
    (ρ : Multiplicative (ZMod 3) →* MulAut (Multiplicative (ZMod p × ZMod p)))
    (h : Multiplicative (ZMod 3) → ZMod p → ZMod p)
    (_h0 : h (Multiplicative.ofAdd (0 : ZMod 3)) 0 = 0) :
    Function.Bijective
      (fun g : (Multiplicative (ZMod p × ZMod p)) ⋊[ρ] Multiplicative (ZMod 3) =>
        (⟨Multiplicative.ofAdd
          (g.left.toAdd.1, g.left.toAdd.2 + h g.right g.left.toAdd.1),
          g.right⟩ :
          (Multiplicative (ZMod p × ZMod p)) ⋊[ρ] Multiplicative (ZMod 3))) := by
  let q : (Multiplicative (ZMod p × ZMod p)) ⋊[ρ] Multiplicative (ZMod 3) →
      (Multiplicative (ZMod p × ZMod p)) ⋊[ρ] Multiplicative (ZMod 3) := fun g =>
    ⟨Multiplicative.ofAdd
      (g.left.toAdd.1, g.left.toAdd.2 + h g.right g.left.toAdd.1),
      g.right⟩
  let qi : (Multiplicative (ZMod p × ZMod p)) ⋊[ρ] Multiplicative (ZMod 3) →
      (Multiplicative (ZMod p × ZMod p)) ⋊[ρ] Multiplicative (ZMod 3) := fun g =>
    ⟨Multiplicative.ofAdd
      (g.left.toAdd.1, g.left.toAdd.2 - h g.right g.left.toAdd.1),
      g.right⟩
  have hq : q = (fun g =>
      (⟨Multiplicative.ofAdd
        (g.left.toAdd.1, g.left.toAdd.2 + h g.right g.left.toAdd.1),
        g.right⟩ :
        (Multiplicative (ZMod p × ZMod p)) ⋊[ρ] Multiplicative (ZMod 3))) := rfl
  rw [← hq]
  constructor
  · intro a b hab
    have hfirst : a.left.toAdd.1 = b.left.toAdd.1 := by
      simpa [q] using congrArg (fun g => g.left.toAdd.1) hab
    have hright : a.right = b.right := by
      simpa [q] using congrArg SemidirectProduct.right hab
    have hsecond :
        a.left.toAdd.2 + h a.right a.left.toAdd.1 =
          b.left.toAdd.2 + h b.right b.left.toAdd.1 := by
      simpa [q] using congrArg (fun g => g.left.toAdd.2) hab
    apply SemidirectProduct.ext
    · apply Multiplicative.ext
      apply Prod.ext
      · exact hfirst
      · simpa [hright, hfirst] using hsecond
    · exact hright
  · intro b
    refine ⟨qi b, ?_⟩
    apply SemidirectProduct.ext
    · apply Multiplicative.ext
      apply Prod.ext
      · rfl
      · simp [q, qi]
    · rfl

end MathlibPlus.GroupTheory
