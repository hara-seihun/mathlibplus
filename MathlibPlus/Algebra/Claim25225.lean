import Mathlib

namespace MathlibPlus.Algebra.Claim25225

/-- The exact two recurrence identities in claim 25225, with the tree and root
indices kept abstract because the source packet does not fix their types. -/
def affineMomentRecursion_claim25225
    {T R : Type*} (a q : ℝ) (nu : T → ℝ)
    (rho eta p : T → R → ℝ) : Prop :=
  ∀ t r, nu t = (a - 1) * rho t r + (q - a) * eta t r ∧
    p t r = rho t r + nu t

/-- The displayed equivalent identity `nu_T = p_{T,r} - rho_{T,r}` follows
from the two exact recurrence identities, and conversely adds no content. -/
theorem affineMomentRecursion_equiv_claim25225
    {T R : Type*} (a q : ℝ) (nu : T → ℝ)
    (rho eta p : T → R → ℝ) :
    affineMomentRecursion_claim25225 a q nu rho eta p ↔
      ∀ t r, nu t = (a - 1) * rho t r + (q - a) * eta t r ∧
        p t r = rho t r + nu t ∧
        nu t = p t r - rho t r := by
  constructor
  · intro h t r
    rcases h t r with ⟨hν, hp⟩
    refine ⟨hν, hp, ?_⟩
    linarith
  · intro h t r
    exact ⟨(h t r).1, (h t r).2.1⟩

end MathlibPlus.Algebra.Claim25225
