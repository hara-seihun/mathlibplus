import Mathlib

namespace MathlibPlus.Algebra.Claim41959

/-!
The source's `𝔽_p²` is represented by `ZMod p × ZMod p`.  The four affine
maps and the two generated permutation subgroups are definitions only; no
regularity or classification assertion is added, since claim 41959 stops at
this construction.
-/

abbrev V (p : ℕ) := ZMod p × ZMod p

def t₁ (p : ℕ) : V p ≃ V p :=
  { toFun := fun z => (z.1 + 1, z.2)
    invFun := fun z => (z.1 - 1, z.2)
    left_inv := by
      intro z
      ext <;> simp
    right_inv := by
      intro z
      ext <;> simp }

def t₂ (p : ℕ) : V p ≃ V p :=
  { toFun := fun z => (z.1, z.2 + 1)
    invFun := fun z => (z.1, z.2 - 1)
    left_inv := by
      intro z
      ext <;> simp
    right_inv := by
      intro z
      ext <;> simp }

def q₁ (p : ℕ) : V p ≃ V p :=
  { toFun := fun z => (z.1 + 1, z.2 + z.1)
    invFun := fun z => (z.1 - 1, z.2 - (z.1 - 1))
    left_inv := by
      intro z
      ext <;> simp
    right_inv := by
      intro z
      ext <;> simp }

def q₂ (p : ℕ) : V p ≃ V p := t₂ p

def P (p : ℕ) : Subgroup (Equiv.Perm (V p)) :=
  Subgroup.closure ({t₁ p, t₂ p} : Set (Equiv.Perm (V p)))

def Q (p : ℕ) : Subgroup (Equiv.Perm (V p)) :=
  Subgroup.closure ({q₁ p, q₂ p} : Set (Equiv.Perm (V p)))

end MathlibPlus.Algebra.Claim41959
