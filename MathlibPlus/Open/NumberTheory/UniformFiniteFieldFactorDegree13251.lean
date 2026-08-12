import Mathlib

namespace MathlibPlus.Open.NumberTheory

/--
The finite-field factor-degree assertion in admitted claim 13251.  The order
predicate is stated by its least-positive-residue characterization, and the
second conjunct records the eventual degree and degree-ratio consequences.
-/
def uniformFiniteFieldFactorDegree_13251 : Prop :=
  ∀ (p : ℕ) (hp : Nat.Prime p) (hp3 : p ≠ 3),
    letI : Fact (Nat.Prime p) := ⟨hp⟩
    let ordSet : ℕ → Set ℕ := fun m =>
      {n | 0 < n ∧ Nat.ModEq m (p ^ n) 1}
    (∀ (k : ℕ), 1 ≤ k →
      ∀ (o : ℕ), IsLeast (ordSet (3 ^ k)) o →
        ∀ q : Polynomial (ZMod p),
          Irreducible q →
          q ∣ Polynomial.cyclotomic (3 ^ k) (ZMod p) →
          q.natDegree = o) ∧
    (∀ (f c k : ℕ),
      1 ≤ c → c < k →
      IsLeast (ordSet 3) f →
      Nat.factorization (p ^ f - 1) 3 = c →
      ∀ (o : ℕ), IsLeast (ordSet (3 ^ k)) o →
        o = f * 3 ^ (k - c) ∧
        0 < ((o : ℚ) / (2 * 3 ^ (k - 1))) ∧
        ((o : ℚ) / (2 * 3 ^ (k - 1))) =
          (f : ℚ) / (2 * 3 ^ (c - 1)))

end MathlibPlus.Open.NumberTheory
