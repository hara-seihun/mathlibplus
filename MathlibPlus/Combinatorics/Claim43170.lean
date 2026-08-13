import MathlibPlus.Basic

namespace MathlibPlus.Combinatorics.Claim43170

/-!
Claim 43170 uses an 89-element nonidentity carrier.  `Fin 89` is the explicit
finite carrier for the cardinality statements below; the group operation and
inversion action are intentionally not reconstructed from the packet.
-/

/-- Five singleton inversion atoms and forty-two paired atoms account for 89 elements. -/
theorem inversionAtomArithmetic :
    5 + 42 = 47 ∧ 5 + 2 * 42 = 89 := by
  norm_num

/-- Complements in the 89-element nonidentity carrier have the stated cardinality. -/
theorem complementCardinality (S : Finset (Fin 89)) :
    Sᶜ.card = 89 - S.card := by
  simpa using Finset.card_compl S

/-- The listed valencies have the listed complement valencies. -/
theorem listedValencyComplements :
    89 - 21 = 68 ∧ 89 - 22 = 67 ∧ 89 - 23 = 66 ∧
      89 - 24 = 65 ∧ 89 - 25 = 64 ∧ 89 - 26 = 63 ∧ 89 - 27 = 62 := by
  norm_num

end MathlibPlus.Combinatorics.Claim43170
