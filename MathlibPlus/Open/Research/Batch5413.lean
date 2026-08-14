import Mathlib

namespace MathlibPlus.Open.Research

section

variable {R : Type*} [CommRing R]

/-- The complete homogeneous polynomial in three variables of degree `n`. -/
def completeHomogeneous (x y z : R) (n : ℕ) : R :=
  ∑ a ∈ Finset.range (n + 1),
    ∑ b ∈ Finset.range (n - a + 1),
      x ^ a * y ^ b * z ^ (n - a - b)

/-- The two-entry column from the admitted claim. -/
def recurrenceColumn (p x y z : R) (n : ℕ) : Fin 2 → R :=
  ![p ^ n, completeHomogeneous x y z n]

/-- The monic order-four recurrence with characteristic polynomial
`(T - p) (T - x) (T - y) (T - z)`. -/
def satisfiesCharacteristicRecurrence (p x y z : R) (s : ℕ → R) : Prop :=
  ∀ n : ℕ,
    s (n + 4)
        - (p + x + y + z) * s (n + 3)
        + (p * x + p * y + p * z + x * y + x * z + y * z) * s (n + 2)
        - (p * x * y + p * x * z + p * y * z + x * y * z) * s (n + 1)
        + p * x * y * z * s n = 0

/-- Generation by the first four columns, over the coefficient ring. -/
def generatedByFirstFour (v : ℕ → Fin 2 → R) : Prop :=
  ∀ n : ℕ,
    v n ∈ Submodule.span R (Set.range (fun i : Fin 4 => v (i : ℕ)))

/-- The bracket `v_a ∧ v_b`, with the determinant convention in the packet. -/
def recurrenceBracket (p x y z : R) (a b : ℕ) : R :=
  (recurrenceColumn p x y z b) 0 * (recurrenceColumn p x y z a) 1
    - (recurrenceColumn p x y z a) 0 * (recurrenceColumn p x y z b) 1

/-- Generation by the six initial minors indexed by `0 ≤ i < j ≤ 3`. -/
def generatedBySixBrackets (bracket : ℕ → ℕ → R) : Prop :=
  ∀ (a b : ℕ),
    a < b →
      bracket a b ∈
        Submodule.span R
          {bracket 0 1, bracket 0 2, bracket 0 3,
            bracket 1 2, bracket 1 3, bracket 2 3}

/--
The common order-four recurrence and six-state exterior-square claim.

Here `x = A²`, `y = B²`, `z = M²`, and `p = P²`; the columns and
brackets are the packet's `v_k` and `𝓑_{a,b}`.  This is intentionally a
proof-free open proposition.
-/
def commonOrderFourRecurrenceAndSixStateExteriorSquare (A B M P : R) : Prop :=
  let x := A ^ 2
  let y := B ^ 2
  let z := M ^ 2
  let p := P ^ 2
  let v : ℕ → Fin 2 → R := recurrenceColumn p x y z
  let bracket : ℕ → ℕ → R := recurrenceBracket p x y z
  (∀ j : Fin 2, satisfiesCharacteristicRecurrence p x y z (fun n => v n j)) ∧
    generatedByFirstFour v ∧
      generatedBySixBrackets bracket

end

end MathlibPlus.Open.Research
