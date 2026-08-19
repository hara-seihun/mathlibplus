import Mathlib

namespace MathlibPlus.Open.NumberTheory.Claim44720

abbrev X1Kernel := Multiplicative (Fin 2 → ZMod 2)
abbrev X1Quotient := Multiplicative (ZMod 9)
abbrev X1Action := X1Quotient →* MulAut X1Kernel

/-- The fixed-point-free order-three condition on the quotient generator used
by the actual X1 semidirect-product carrier. -/
def fixedPointFreeX1Action (φ : X1Action) : Prop :=
  ∀ v : X1Kernel, φ (.ofAdd 1) v = v → v = 1

/-- A cyclic subgroup is represented by an actual generator and integral
powers, without replacing the subgroup by an unconstrained proposition. -/
def cyclicSubgroup44720 {G : Type*} [Group G]
    (N : Subgroup G) : Prop :=
  ∃ n : G, ∀ x : G, x ∈ N → ∃ k : ℤ, x = n ^ k

/-- The quotient by a normal subgroup is cyclic, written directly by its
coset-generation relation on the actual ambient group. -/
def cyclicQuotient44720 {G : Type*} [Group G]
    (N : Subgroup G) : Prop :=
  ∃ g : G, ∀ x : G, ∃ k : ℤ, x * (g ^ k)⁻¹ ∈ N

/-- Exact metacyclic carrier used by the restricted negative theorem. -/
def metacyclic44720 (G : Type*) [Group G] : Prop :=
  ∃ N : Subgroup G,
    N.Normal ∧ cyclicSubgroup44720 N ∧ cyclicQuotient44720 N

def metacyclicOrder9p44720 (G : Type*) [Group G] : Prop :=
  ∃ p : ℕ,
    Nat.Prime p ∧ Odd p ∧ Nat.card G = 9 * p ∧ metacyclic44720 G

/-- Claim 44720: the actual fixed-point-free X1 semidirect carrier has order
36 and center order 3, while the restricted odd-prime order-`9p` theorem has
no applicable parameter. -/
def claim44720_x1OutsideOddPrimeMetacyclicRange : Prop :=
  (∀ p : ℕ, Nat.Prime p → Odd p → 36 ≠ 9 * p) ∧
    ∀ φ : X1Action,
      fixedPointFreeX1Action φ →
        let G := SemidirectProduct X1Kernel X1Quotient φ
        Nat.card G = 36 ∧
          Nat.card (Subgroup.center G) = 3 ∧
          (∀ p : ℕ, Nat.Prime p → Odd p → Nat.card G ≠ 9 * p) ∧
          ¬ metacyclicOrder9p44720 G

end MathlibPlus.Open.NumberTheory.Claim44720
