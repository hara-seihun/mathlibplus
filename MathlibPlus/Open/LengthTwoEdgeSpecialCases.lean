import Mathlib

namespace MathlibPlus.Open

/--
At an edge of length two there is one integral interior split.  The two
endpoint rows therefore coincide: their pendant difference is zero, while
negating their internal sum has coefficient `-2` at that split.
-/
def lengthTwoEdgeSpecialCases : Prop :=
  let edgeLength : ℕ := 2
  let splitRows : Type := Fin (edgeLength - 1) → ℤ
  let deltaL : splitRows := fun _ => 1
  let deltaR : splitRows := fun _ => 1
  let pendantCurvature : splitRows := deltaR - deltaL
  let internalCurvature : splitRows := -(deltaL + deltaR)
  pendantCurvature = 0 ∧ internalCurvature = fun _ => (-2 : ℤ)

end MathlibPlus.Open
