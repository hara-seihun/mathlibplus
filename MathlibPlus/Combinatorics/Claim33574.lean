import Mathlib.Data.ZMod.Basic

namespace MathlibPlus.Combinatorics.Claim33574

/-!
Formalization of admitted claim 33574.

The Cartesian parameter type makes the three factors in the source count
explicit: normalized middle carries, nonzero points of `𝔽₃³`, and nonzero
values in `𝔽₃`. The source's "degree-729" is a label for this finite family;
no separate degree object is introduced here.
-/

/-- There are `3^8` normalized middle carries, `26 · 2 = 52` one-point
nonzero top carries, and consequently `341172` members of the complete
single-top parameter family. -/
theorem completeSingleTopFamilyCount :
    Fintype.card {q : (ZMod 3 × ZMod 3) → ZMod 3 // q (0, 0) = 0} = 3 ^ 8 ∧
      Fintype.card
          ({x : Fin 3 → ZMod 3 // x ≠ 0} × {c : ZMod 3 // c ≠ 0}) = 52 ∧
      Fintype.card
          ({q : (ZMod 3 × ZMod 3) → ZMod 3 // q (0, 0) = 0} ×
            ({x : Fin 3 → ZMod 3 // x ≠ 0} × {c : ZMod 3 // c ≠ 0})) = 341172 := by
  native_decide

end MathlibPlus.Combinatorics.Claim33574
