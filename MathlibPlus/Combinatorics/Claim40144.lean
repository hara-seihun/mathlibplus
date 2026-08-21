-- UNVERIFIED (native-decide): submitted but not kernel-verified, so it is not built and MathlibPlus.lean does not import it. See unverified.txt.
import Mathlib

namespace MathlibPlus.Combinatorics.Claim40144

/-! The source identifies these as the nonzero vectors of `C₂³` and its
transpositions.  We use the literal finite vector space and unordered
2-subsets, so the count does not depend on a choice of permutation encoding. -/

theorem nonzeroVector_card :
    let V := Fin 3 → ZMod 2
    Fintype.card {v : V // v ≠ 0} = 7 := by
  native_decide

theorem transposition_card :
    let V := Fin 3 → ZMod 2
    let NonzeroV := {v : V // v ≠ 0}
    Fintype.card {s : Finset NonzeroV // s.card = 2} = 21 := by
  native_decide

theorem chartAlphabet_card :
    let V := Fin 3 → ZMod 2
    let NonzeroV := {v : V // v ≠ 0}
    let Transposition := {s : Finset NonzeroV // s.card = 2}
    Fintype.card (Unit ⊕ Transposition) = 22 := by
  native_decide

end MathlibPlus.Combinatorics.Claim40144
