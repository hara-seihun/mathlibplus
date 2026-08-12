import Mathlib

namespace MathlibPlus.Algebra.Claim27552

/-!
Formalization of admitted claim 27552.

The source describes an active fiber over a finite elementary abelian
2-group.  The displayed identities use only the additive exponent-two law,
so the formalization retains that law explicitly and allows an arbitrary
permutation `p` of the fiber.  Composition is function composition, and the
inverses occurring in the two displayed restrictions are written explicitly.
-/

/-- The three transition derivatives and the two stated restrictions. -/
theorem transitionRestrictions
    {V : Type*} [AddCommGroup V]
    (h2 : ∀ x : V, x + x = 0) (p : V ≃ V) :
    let τ : V → V → V := fun a x => x + a
    let F : V → V → V := fun u x => p.symm (τ u (p (τ u x)))
    let G : V → V → V := fun u x => p.symm (τ (u + p u) x)
    let H : V → V → V := fun u x => p.symm (τ (p u) (p (τ u x)))
    let FInv : V → V → V := fun u x => τ u (p.symm (τ u (p x)))
    let G0Inv : V → V := fun x => p x + p 0
    (∀ u : V, (F u) ∘ (FInv u) = id ∧ (FInv u) ∘ (F u) = id) ∧
      (∀ u : V, (H u) ∘ (FInv u) =
        fun x => p.symm (p x + (u + p u))) ∧
      (∀ u : V, (G u) ∘ G0Inv =
        fun x => p.symm (p x + (u + p u + p 0))) := by
  dsimp
  have hinv : ∀ a x : V, (x + a) + a = x := by
    intro a x
    calc
      (x + a) + a = x + (a + a) := by rw [add_assoc]
      _ = x := by rw [h2 a, add_zero]
  constructor
  · intro u
    constructor
    · funext x
      dsimp [Function.comp]
      rw [hinv u (p.symm (p x + u))]
      rw [p.apply_symm_apply]
      rw [hinv u (p x)]
      rw [p.symm_apply_apply]
    · funext x
      dsimp [Function.comp]
      rw [p.apply_symm_apply]
      rw [hinv u (p (x + u))]
      rw [p.symm_apply_apply]
      rw [hinv u x]
  · constructor
    · intro u
      funext x
      dsimp [Function.comp]
      rw [hinv u (p.symm (p x + u))]
      rw [p.apply_symm_apply]
      congr 1
      abel
    · intro u
      funext x
      dsimp [Function.comp]
      congr 1
      abel

end MathlibPlus.Algebra.Claim27552
