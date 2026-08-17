import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.BatchR1302

noncomputable section

abbrev ProductPoint (r s : ℕ) := ZMod r × ZMod s

/-- The four literal maps in the `F_r × Z_s` construction. -/
def pFunction (r s : ℕ) : ProductPoint r s → ProductPoint r s :=
  fun p => (p.1 + 1, p.2)

def sFunction (r s : ℕ) : ProductPoint r s → ProductPoint r s :=
  fun p => (p.1, p.2 + 1)

def qFunction {r s : ℕ} (u : ZMod s → (ZMod r)ˣ) :
    ProductPoint r s → ProductPoint r s :=
  fun p => (p.1 + (u p.2 : ZMod r), p.2)

def hFunction {r s : ℕ} (u : ZMod s → (ZMod r)ˣ) :
    ProductPoint r s → ProductPoint r s :=
  fun p =>
    (((u (p.2 + 1) / u p.2 : (ZMod r)ˣ) : ZMod r) * p.1, p.2 + 1)

def generatedBy {X : Type*} (g h : Equiv.Perm X) :
    Subgroup (Equiv.Perm X) :=
  Subgroup.closure ({g, h} : Set (Equiv.Perm X))

def regularSubgroupOn {X : Type*}
    (K : Subgroup (Equiv.Perm X)) : Prop :=
  ∀ x y : X, ∃! g : K, g.1 x = y

def regularCyclicOfOrder {X : Type*}
    (K : Subgroup (Equiv.Perm X)) (n : ℕ) : Prop :=
  Nat.card K = n ∧ IsCyclic K ∧ regularSubgroupOn K

def outerBlock {r s : ℕ} (j : ZMod s) : Set (ProductPoint r s) :=
  {p | p.2 = j}

def outerBlockSystem (r s : ℕ) : Set (Set (ProductPoint r s)) :=
  {B | ∃ j : ZMod s, B = outerBlock j}

def subgroupOrbit {X : Type*}
    (K : Subgroup (Equiv.Perm X)) (x : X) : Set X :=
  {y | ∃ g : K, g.1 x = y}

def subgroupOrbitSystem {X : Type*}
    (K : Subgroup (Equiv.Perm X)) : Set (Set X) :=
  {B | ∃ x : X, B = subgroupOrbit K x}

def localRestrictionSet {r s : ℕ}
    (K : Subgroup (Equiv.Perm (ProductPoint r s))) (j : ZMod s) :
    Set (ZMod r → ZMod r) :=
  {f | ∃ g : K, ∀ x : ZMod r, g.1 (x, j) = (f x, j)}

def sameLocalRestrictionGroups {r s : ℕ}
    (K L : Subgroup (Equiv.Perm (ProductPoint r s))) : Prop :=
  ∀ j : ZMod s, localRestrictionSet K j = localRestrictionSet L j

def sameQuotientAction {r s : ℕ}
    (K L : Subgroup (Equiv.Perm (ProductPoint r s))) : Prop :=
  (∀ g : K, ∃ h : L, ∀ x, (g.1 x).2 = (h.1 x).2) ∧
    (∀ h : L, ∃ g : K, ∀ x, (h.1 x).2 = (g.1 x).2)

def characteristicIn {X : Type*}
    (K L : Subgroup (Equiv.Perm X)) : Prop :=
  L ≤ K ∧ ∀ e : MulEquiv K K, ∀ x : K, x.1 ∈ L → (e x).1 ∈ L

def characteristicOrderSubgroup {X : Type*}
    (K L : Subgroup (Equiv.Perm X)) (n : ℕ) : Prop :=
  L ≤ K ∧ Nat.card L = n ∧ characteristicIn K L

/-- Claim 41171: the explicit maps form the two regular cyclic copies, with
common block, local-restriction, and quotient data but distinct global
characteristic order-r subgroups. -/
def explicitCyclicBlockCopies_claim41171 : Prop :=
  ∀ (r s : ℕ) [Fact (Nat.Prime r)] [Fact (Nat.Prime s)],
    Odd r → r ≠ s →
    ∀ (u : ZMod s → (ZMod r)ˣ),
      (∃ i j : ZMod s, u i ≠ u j) →
      ∃ P S Q H : Equiv.Perm (ProductPoint r s),
        (∀ x : ZMod r, ∀ j : ZMod s,
          P (x, j) = pFunction r s (x, j)) ∧
        (∀ x : ZMod r, ∀ j : ZMod s,
          S (x, j) = sFunction r s (x, j)) ∧
        (∀ x : ZMod r, ∀ j : ZMod s,
          Q (x, j) = qFunction u (x, j)) ∧
        (∀ x : ZMod r, ∀ j : ZMod s,
          H (x, j) = hFunction u (x, j)) ∧
        (∀ x, P (S x) = S (P x)) ∧
        (∀ x, Q (H x) = H (Q x)) ∧
        H ^ s = 1 ∧
        regularCyclicOfOrder (generatedBy P S) (r * s) ∧
        regularCyclicOfOrder (generatedBy Q H) (r * s) ∧
        subgroupOrbitSystem (Subgroup.closure
          ({P} : Set (Equiv.Perm (ProductPoint r s)))) =
          outerBlockSystem r s ∧
        subgroupOrbitSystem (Subgroup.closure
          ({Q} : Set (Equiv.Perm (ProductPoint r s)))) =
          outerBlockSystem r s ∧
        (∀ B : Set (ProductPoint r s), B ∈ outerBlockSystem r s →
          Nat.card B = r) ∧
        sameLocalRestrictionGroups
          (Subgroup.closure ({P} : Set (Equiv.Perm (ProductPoint r s))))
          (Subgroup.closure ({Q} : Set (Equiv.Perm (ProductPoint r s)))) ∧
        sameQuotientAction (generatedBy P S) (generatedBy Q H) ∧
        characteristicOrderSubgroup (generatedBy P S)
          (Subgroup.closure ({P} : Set (Equiv.Perm (ProductPoint r s)))) r ∧
        characteristicOrderSubgroup (generatedBy Q H)
          (Subgroup.closure ({Q} : Set (Equiv.Perm (ProductPoint r s)))) r ∧
        Subgroup.closure ({P} : Set (Equiv.Perm (ProductPoint r s))) ≠
          Subgroup.closure ({Q} : Set (Equiv.Perm (ProductPoint r s))) ∧
        Subgroup.closure ({P} : Set (Equiv.Perm (ProductPoint r s))) ⊓
            Subgroup.closure ({Q} : Set (Equiv.Perm (ProductPoint r s))) = ⊥

end
end MathlibPlus.Open.ResearchFormalization.BatchR1302
