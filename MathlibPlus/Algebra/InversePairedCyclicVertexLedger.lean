import Mathlib

namespace MathlibPlus.Algebra.InversePairedCyclicVertexLedger

/-!
# Inverse-paired cyclic vertex ledger

Claim 13269 supplies four log-moduli in the order `a, b, -b, -a`, with
`a,b > 0`. The surrounding cyclic-vertex semantics are not defined in the
claim text; this file retains the exact four-entry ledger, its two negation
pairings, and its zero total.
-/

/-- The displayed four-entry ledger is inverse-paired and has total zero. -/
theorem inversePairedCyclicVertexLedger (a b : ℝ) (_ha : 0 < a) (_hb : 0 < b) :
    let v : Fin 4 → ℝ := ![a, b, -b, -a]
    v 0 = -v 3 ∧ v 1 = -v 2 ∧
      v 0 + v 1 + v 2 + v 3 = 0 := by
  dsimp
  constructor
  · ring
  constructor <;> ring

end MathlibPlus.Algebra.InversePairedCyclicVertexLedger
