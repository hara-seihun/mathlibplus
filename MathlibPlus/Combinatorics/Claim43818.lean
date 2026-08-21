-- UNVERIFIED (native-decide): submitted but not kernel-verified, so it is a root of the Unverified library rather than of MathlibPlus and no build here depends on it. See unverified.txt.
import Mathlib

namespace MathlibPlus.Combinatorics.Claim43818

/-!
The literal pair model from admitted claim 43818.  The ambient space is
`(F₂ × F₂) × (F₂ × F₂)`, with the first pair denoting `(u,v)` and the second
pair denoting `w`.  The two functions use the section table in the source:
`A_00 = F₂`, `A_w = {0}` otherwise, `B_01 = F₂`, and `B_w = {0}` otherwise.
-/

abbrev V := (ZMod 2 × ZMod 2) × (ZMod 2 × ZMod 2)

def pairA (x : V) : Bool :=
  decide (x.2 = (0, 0) ∨ x.1.2 = 0)

def pairB (x : V) : Bool :=
  decide (x.2 = (0, 1) ∨ x.1.1 = 0)

def pairProduct (x : V) : Bool := pairA x && pairB x

def translate (x : V) : V :=
  ((x.1.1 + 1, x.1.2 + 1), x.2)

def translateProduct (x : V) : Bool := pairProduct (translate x)

def density (f : V → Bool) : ℚ :=
  (∑ x : V, if f x then (1 : ℚ) else 0) / (Fintype.card V : ℚ)

/-- The first explicit section function has ten true values out of sixteen. -/
theorem pairA_density : density pairA = 5 / 8 := by
  native_decide

/-- The second explicit section function has ten true values out of sixteen. -/
theorem pairB_density : density pairB = 5 / 8 := by
  native_decide

/-- Their pointwise product has six true values out of sixteen. -/
theorem pairProduct_density : density pairProduct = 3 / 8 := by
  native_decide

/-- The pair-product support is disjoint from its translate by `(1,1,0,0)`. -/
theorem pairProduct_translate_disjoint :
    ∀ x : V, pairProduct x = true → translateProduct x = false := by
  native_decide

end MathlibPlus.Combinatorics.Claim43818
