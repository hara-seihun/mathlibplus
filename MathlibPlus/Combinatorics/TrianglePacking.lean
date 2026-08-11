import Mathlib

namespace MathlibPlus.Combinatorics

/--
Claim 22304.  An explicit injective edge certificate for `P` selected
triangles on `D` descendants has `3 * P` slots and `Nat.choose D 2`
possible edges.  The second displayed bound is the resulting integer
consequence.  The certificate interface deliberately does not invent the
source packet's union-closed-family API.
-/
theorem globalTrianglePackingBound_claim22304
    (P D : ℕ)
    (edge : Fin P × Fin 3 → Fin (Nat.choose D 2))
    (hedge : Function.Injective edge) :
    3 * P ≤ Nat.choose D 2 ∧ P ≤ D * (D - 1) / 6 := by
  have hcard :
      Fintype.card (Fin P × Fin 3) ≤ Fintype.card (Fin (Nat.choose D 2)) :=
    Fintype.card_le_of_injective edge hedge
  have hfirst : P * 3 ≤ Nat.choose D 2 := by
    simpa using hcard
  constructor
  · simpa [Nat.mul_comm] using hfirst
  · have hchoose : 2 * Nat.choose D 2 = D * (D - 1) := by
      rw [Nat.choose_two_right]
      exact Nat.mul_div_cancel' (Nat.even_mul_pred_self D).two_dvd
    have hsix : 6 * P ≤ D * (D - 1) := by
      nlinarith
    omega

end MathlibPlus.Combinatorics
