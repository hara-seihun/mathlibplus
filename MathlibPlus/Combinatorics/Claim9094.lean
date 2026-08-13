import Mathlib

namespace MathlibPlus.Combinatorics

universe u

noncomputable section

/-- If the connected components of a graph are represented by the finite type
`C`, its Boolean component colorings have the exact count `2^|C|`.  The
packet-specific identification of compatible labeled graph pairs with these
colorings remains an explicit source-level interface. -/
def claim9094_booleanComponentColoringCount (C : Type u) [Fintype C] : Prop :=
  letI := Classical.decEq C
  Fintype.card (C → Bool) = 2 ^ Fintype.card C

theorem claim9094_booleanComponentColoringCount_proof (C : Type u) [Fintype C] :
    claim9094_booleanComponentColoringCount C := by
  classical
  unfold claim9094_booleanComponentColoringCount
  rw [Fintype.card_fun, Fintype.card_bool]

end
end MathlibPlus.Combinatorics
