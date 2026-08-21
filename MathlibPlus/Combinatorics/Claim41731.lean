-- UNVERIFIED (native-decide): submitted but not kernel-verified, so it is not built and MathlibPlus.lean does not import it. See unverified.txt.
import Mathlib

namespace MathlibPlus.Combinatorics.Claim41731

/-!
`C₇` is represented by the canonical seven-element type `Fin 7`, with its
modulo-seven multiplication.  The scalar states are the nonzero
multiplications `x ↦ a * x`; the source's phrase "scalar" is otherwise not
specified.
-/

abbrev C7 := Fin 7

def normalizedStates : Finset (Equiv.Perm C7) :=
  Finset.univ.filter (fun δ => δ 0 = 0)

def scalarStates : Finset (Equiv.Perm C7) :=
  normalizedStates.filter (fun δ =>
    ∃ a : C7, a ≠ 0 ∧ ∀ x : C7, δ x = a * x)

/-- The permutations of `C₇` fixing zero are counted by `6!`. -/
theorem card_normalizedStates_claim41731 :
    normalizedStates.card = 720 := by
  native_decide

/-- Exactly the six nonzero scalar multiplications occur among the normalized
states. -/
theorem card_scalarStates_claim41731 : scalarStates.card = 6 := by
  native_decide

/-- The complement of the scalar states has the remaining `714` elements. -/
theorem card_nonlinearStates_claim41731 :
    (normalizedStates \ scalarStates).card = 714 := by
  have hs : scalarStates ⊆ normalizedStates := by
    intro δ hδ
    exact (Finset.mem_filter.mp hδ).1
  rw [Finset.card_sdiff]
  rw [Finset.inter_eq_left.mpr hs]
  rw [card_normalizedStates_claim41731, card_scalarStates_claim41731]

end MathlibPlus.Combinatorics.Claim41731
