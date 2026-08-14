import Mathlib

namespace MathlibPlus.Open.GraphTheory

/-- Claim 21811: invariance under a 43-cycle yields a 43-vertex circulant. -/
def invariant43CycleYieldsCirculant : Prop :=
  ∀ G : SimpleGraph (ZMod 43),
    (∀ x y : ZMod 43, G.Adj (x + 1) (y + 1) ↔ G.Adj x y) →
      ∃ S : Finset (Fin 21),
        ∀ x y : ZMod 43,
          G.Adj x y ↔
            ∃ d : Fin 21,
              d ∈ S ∧
                (x - y = ((d.val + 1 : ℕ) : ZMod 43) ∨
                  x - y = -((d.val + 1 : ℕ) : ZMod 43))

/-- The Ramsey `(5,5)` condition used by Claim 21812. -/
private def isGood55 (G : SimpleGraph (ZMod 43)) : Prop :=
  (¬ ∃ s : Finset (ZMod 43),
      s.card = 5 ∧
        ∀ ⦃x : ZMod 43⦄, x ∈ s →
          ∀ ⦃y : ZMod 43⦄, y ∈ s → x ≠ y → G.Adj x y) ∧
  (¬ ∃ s : Finset (ZMod 43),
      s.card = 5 ∧
        ∀ ⦃x : ZMod 43⦄, x ∈ s →
          ∀ ⦃y : ZMod 43⦄, y ∈ s → x ≠ y → ¬G.Adj x y)

/-- Fixed-point-free graph automorphisms whose permutation order is prime. -/
private def hasFixedPointFreePrimeOrderAutomorphism (G : SimpleGraph (ZMod 43)) : Prop :=
  ∃ σ : Equiv.Perm (ZMod 43),
    (∀ x y : ZMod 43, G.Adj (σ x) (σ y) ↔ G.Adj x y) ∧
      (∀ x : ZMod 43, σ x ≠ x) ∧ Nat.Prime (orderOf σ)

/-- Claim 21812: no good 43-vertex circulant, hence no good graph with such an automorphism. -/
def noGood43CirculantOrPrimeOrderAutomorphism : Prop :=
  (∀ G : SimpleGraph (ZMod 43),
      (∃ S : Finset (Fin 21),
        ∀ x y : ZMod 43,
          G.Adj x y ↔
            ∃ d : Fin 21,
              d ∈ S ∧
                (x - y = ((d.val + 1 : ℕ) : ZMod 43) ∨
                  x - y = -((d.val + 1 : ℕ) : ZMod 43))) →
        ¬isGood55 G) ∧
    (∀ G : SimpleGraph (ZMod 43),
      isGood55 G → ¬hasFixedPointFreePrimeOrderAutomorphism G)

end MathlibPlus.Open.GraphTheory
