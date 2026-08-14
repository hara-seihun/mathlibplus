import Mathlib

namespace MathlibPlus.Open

noncomputable section

open Classical
private abbrev F7 := ZMod 7
local instance : DecidableEq F7 := Classical.decEq _

private def inputIndex (x : F7) (hx : x ≠ 0) : Fin 6 :=
  ⟨x.val - 1, by
    have hpos : 0 < x.val := Nat.pos_of_ne_zero (by
      intro hzero
      exact hx ((ZMod.val_eq_zero x).mp hzero))
    have hlt : x.val < 7 := ZMod.val_lt x
    omega⟩

private def normalizedValue (v : Fin 3 × Fin 6 → F7) (k : Fin 3) (x : F7) : F7 :=
  if hx : x = 0 then 0 else v (k, inputIndex x hx)

private def voltageResidual (v : Fin 3 × Fin 6 → F7) (x u : F7) : F7 :=
  normalizedValue v 2 (x + 3 * u) - normalizedValue v 2 x
    - normalizedValue v 0 (x + 2 * u) + normalizedValue v 0 (x + 3 * u)
    + 2 * normalizedValue v 1 u

private def voltageBasis (j : Fin 3 × Fin 6) : Fin 3 × Fin 6 → F7 :=
  fun k => if k = j then 1 else 0

private def voltageMatrix : Matrix (F7 × F7) (Fin 3 × Fin 6) F7 :=
  fun row col => voltageResidual (voltageBasis col) row.1 row.2

private def voltageEquation (b c t : F7 → F7) : Prop :=
  ∀ x u : F7,
    t (x + 3 * u) - t x = b (x + 2 * u) - b (x + 3 * u) - 2 * c u

private def voltageSolution (b c t : F7 → F7) : Prop :=
  b 0 = 0 ∧ c 0 = 0 ∧ t 0 = 0 ∧ voltageEquation b c t

private def quadraticSolution (α β ε : F7) :
    (F7 → F7) × (F7 → F7) × (F7 → F7) :=
  ( (fun x => α * x + β * x ^ 2),
    (fun x => (3 * α + 2 * ε) * x + 6 * β * x ^ 2),
    (fun x => ε * x + 2 * β * x ^ 2) )

private def quadraticNonlinear
    (v : (F7 → F7) × (F7 → F7) × (F7 → F7)) : Prop :=
  voltageSolution v.1 v.2.1 v.2.2 ∧
    ∃ α β ε : F7, β ≠ 0 ∧ v = quadraticSolution α β ε

/-- Claim 29141: the normalized 49-equation voltage system has rank 15 and
its solutions are exactly the displayed quadratic family, with the stated
row counts. -/
def claim_29141 : Prop :=
  Fintype.card (F7 × F7) = 49 ∧
  Fintype.card (Fin 3 × Fin 6) = 18 ∧
  Matrix.rank voltageMatrix = 15 ∧
  (∀ b c t : F7 → F7,
    voltageSolution b c t ↔
      ∃ α β ε : F7,
        (b, c, t) = quadraticSolution α β ε) ∧
  Fintype.card
      {v : (F7 → F7) × (F7 → F7) × (F7 → F7) //
        voltageSolution v.1 v.2.1 v.2.2} = 343 ∧
  Fintype.card
      {v : (F7 → F7) × (F7 → F7) × (F7 → F7) // quadraticNonlinear v} = 294

private def primePower (n : Nat) : Prop :=
  ∃ p k : Nat, Nat.Prime p ∧ 1 ≤ k ∧ n = p ^ k

private def powerOf27 (n : Nat) : Prop :=
  ∃ d : Nat, 1 ≤ d ∧ n = 27 ^ d

/-- Claim 29190: the order of a nontrivial finite odd-order group times Q₈
has both even and odd prime divisors, excluding the two stated degree forms. -/
def claim_29190 : Prop :=
  ∀ (A : Type*) [Fintype A] [Group A] [Nontrivial A],
    Odd (Fintype.card A) →
      let n := Fintype.card (A × QuaternionGroup 2)
      Fintype.card (A × QuaternionGroup 2) = 8 * Fintype.card A ∧
        (∃ p : Nat, Nat.Prime p ∧ Even p ∧ p ∣ n) ∧
        (∃ p : Nat, Nat.Prime p ∧ Odd p ∧ p ∣ n) ∧
        ¬ primePower n ∧ ¬ powerOf27 n

end
end MathlibPlus.Open
