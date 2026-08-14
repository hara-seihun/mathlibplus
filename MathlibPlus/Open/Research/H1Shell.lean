import Mathlib

namespace MathlibPlus.Open.Research

/-- A Sylow subgroup is elementary abelian exactly when it is abelian and
all of its elements have exponent dividing the relevant prime. -/
def elementaryAbelianSylow (p : ℕ) {G : Type*} [Group G]
    (P : Sylow p G) : Prop :=
  (∀ x y : P, x * y = y * x) ∧ ∀ x : P, x ^ p = 1

/-- The mixed abelian part of the `H1` candidate shell through order `108`:
there are at least two support primes, every odd Sylow subgroup is
 elementary abelian, and the Sylow-2 subgroups are elementary abelian or
cyclic of order four. -/
def mixedAbelianH1Shell (G : Type*) [Fintype G] [CommGroup G] : Prop :=
  2 ≤ (Nat.primeFactors (Fintype.card G)).card ∧
    Fintype.card G ≤ 108 ∧
    (∀ p : ℕ, Nat.Prime p → p % 2 = 1 → p ∣ Fintype.card G →
      ∀ P : Sylow p G, elementaryAbelianSylow p P) ∧
    (∀ P : Sylow 2 G,
      elementaryAbelianSylow 2 P ∨ (IsCyclic P ∧ Nat.card P = 4))

end MathlibPlus.Open.Research
