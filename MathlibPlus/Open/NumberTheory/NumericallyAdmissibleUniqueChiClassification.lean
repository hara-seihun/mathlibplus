import Mathlib

namespace MathlibPlus.Open.NumberTheory

/-- The integer pairs satisfying the five admissibility conditions in Claim 59538. -/
def numericallyAdmissiblePair (k c : ℤ) : Prop :=
  k > 0 ∧ c > 0 ∧ 12 ∣ k + c ∧ 5 * k ≥ c - 36 ∧ k ≤ 3 * c

/--
Claim 59538: the admissibility conditions are equivalent to the unique parameter
range, together with the asserted count at each positive parameter.
-/
def numericallyAdmissibleUniqueChiClassification : Prop :=
  (∀ k c : ℤ,
    numericallyAdmissiblePair k c ↔
      ∃! a : ℤ,
        a ≥ 1 ∧
        c = 12 * a - k ∧
        max (1 : ℤ) (2 * a - 6) ≤ k ∧
        k ≤ 9 * a) ∧
  (∀ a : ℤ, a ≥ 1 →
    Set.ncard
        {p : ℤ × ℤ |
          numericallyAdmissiblePair p.1 p.2 ∧
            (p.1 + p.2) / 12 = a} =
      if a ≤ 3 then Int.toNat (9 * a) else Int.toNat (7 * a + 7))

end MathlibPlus.Open.NumberTheory
