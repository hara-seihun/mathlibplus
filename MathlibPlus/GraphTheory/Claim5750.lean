-- UNVERIFIED (native-decide): submitted but not kernel-verified, so it is not built and MathlibPlus.lean does not import it. See unverified.txt.
import Mathlib

open scoped BigOperators

namespace MathlibPlus.GraphTheory

/-- Claim 5750: the three two-edge spanning paths and the full triangle are
exactly the connected spanning edge subsets of the explicit `K₃` model.
The three edge indices are mapped to the three unordered vertex pairs, and
`SimpleGraph.Connected` supplies the source notion of connectivity. -/
theorem triangleConnectedSpanningCounts_claim5750 :
    let adjacent : Finset (Fin 3) → Fin 3 → Fin 3 → Bool := fun s v w =>
      (((v = 0 ∧ w = 1) ∨ (v = 1 ∧ w = 0)) && (0 ∈ s)) ||
      (((v = 0 ∧ w = 2) ∨ (v = 2 ∧ w = 0)) && (1 ∈ s)) ||
      (((v = 1 ∧ w = 2) ∨ (v = 2 ∧ w = 1)) && (2 ∈ s))
    let G : Finset (Fin 3) → SimpleGraph (Fin 3) := fun s =>
      SimpleGraph.fromRel (fun v w => adjacent s v w = true)
    let C := (Finset.univ : Finset (Finset (Fin 3))).filter (fun s => decide (G s).Connected)
    C.card = 4 ∧
      (C.filter (fun s => s.card = 2)).card = 3 ∧
      (C.filter (fun s => s.card = 3)).card = 1 ∧
      (∑ s ∈ C, (-1 : ℤ) ^ s.card) = 2 := by
  native_decide

end MathlibPlus.GraphTheory
