import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.BatchR1102

open scoped BigOperators

abbrev F7 := ZMod 7
abbrev Square := F7 × F7

/-- The two normalized factor connection sets `I₂` and `I₄` on `C₇²`. -/
def connectionSet (i : Fin 2) : Set Square :=
  if i = 0 then
    {p | p.1 = 0 ∧ (p.2 = 1 ∨ p.2 = -1)}
  else
    {p | p.1 = 0 ∧
      (p.2 = 1 ∨ p.2 = -1 ∨ p.2 = 2 ∨ p.2 = -2)}

/-- Adjacency in one of the two seven-component Cayley graphs. -/
def factorAdj (i : Fin 2) (x y : Square) : Prop :=
  x ≠ y ∧ (y.1 - x.1, y.2 - x.2) ∈ connectionSet i

/-- The graph complement relation, retaining the irreflexive convention. -/
def graphComplement (adj : Square → Square → Prop)
    (x y : Square) : Prop :=
  x ≠ y ∧ ¬ adj x y

/-- The two explicit GL(2,7) normalizing maps from the retained atlas rows. -/
def normalization17791 (p : Square) : Square :=
  (2 * p.2, p.1 + 4 * p.2)

def normalization17792 (p : Square) : Square :=
  (3 * p.2, p.1 + 6 * p.2)

/-- Image of a graph relation under a displayed coordinate map. -/
def imageRelation (map : Square → Square)
    (adj : Square → Square → Prop) (x y : Square) : Prop :=
  ∃ a b, map a = x ∧ map b = y ∧ adj a b

/-- The four atlas representatives in the order `(1,2,17791,17792)`. -/
def atlasAdj (i : Fin 4) : Square → Square → Prop :=
  if i = 0 then factorAdj 0
  else if i = 1 then factorAdj 1
  else if i = 2 then
    imageRelation normalization17791 (graphComplement (factorAdj 1))
  else
    imageRelation normalization17792 (graphComplement (factorAdj 0))

/-- The same four rows after the displayed GL normalizations.  Thus the last
 two rows are the complements of rows 2 and 1, respectively. -/
def normalizedAdj (i : Fin 4) : Square → Square → Prop :=
  if i = 0 then factorAdj 0
  else if i = 1 then factorAdj 1
  else if i = 2 then graphComplement (factorAdj 1)
  else graphComplement (factorAdj 0)

/-- The numerical labels attached to the four retained rows. -/
def retainedIndex (i : Fin 4) : ℕ :=
  if i = 0 then 1
  else if i = 1 then 2
  else if i = 2 then 17791
  else 17792

/-- A permutation preserving a graph relation. -/
def graphAutomorphism
    (adj : Square → Square → Prop) (σ : Equiv.Perm Square) : Prop :=
  ∀ x y, adj (σ x) (σ y) ↔ adj x y

/-- The affine dihedral action on one `C₇` factor. -/
def dihedralFactor (τ : Equiv.Perm F7) : Prop :=
  ∃ ε b : F7,
    (ε = 1 ∨ ε = -1) ∧ ∀ y, τ y = ε * y + b

/-- The concrete carrier of `D₁₄ wr S₇`: an arbitrary permutation of the
 seven components and an independent affine dihedral action in each one. -/
def wreathDihedral (σ : Equiv.Perm Square) : Prop :=
  ∃ p : Equiv.Perm F7, ∃ ε b : F7 → F7,
    (∀ x, ε x = 1 ∨ ε x = -1) ∧
      ∀ x y, σ (x, y) = (p x, ε x * y + b x)

/-- The order of the displayed wreath product. -/
def wreathOrder : ℕ := 14 ^ 7 * Nat.factorial 7

/-- Every zero-fixing wreath element has the normalized parameter form in the
statement of Claim 28910.  The sole restriction on the translations is
`b 0 = 0`; all other values of `b` are free parameters. -/
def zeroFixingNormalForm (σ : Equiv.Perm Square) : Prop :=
  ∃ p : Equiv.Perm F7, ∃ ε b : F7 → F7,
    p 0 = 0 ∧ b 0 = 0 ∧
      (∀ x, ε x = 1 ∨ ε x = -1) ∧
      ∀ x y, σ (x, y) = (p x, ε x * y + b x)

/-- The zero stabilizer inside the graph automorphism group. -/
def zeroFixingAutomorphism
    (adj : Square → Square → Prop) (σ : Equiv.Perm Square) : Prop :=
  graphAutomorphism adj σ ∧ σ (0, 0) = (0, 0)

/-- Claim 28909: after the explicit normalizations, every graph automorphism
is exactly a component permutation together with seven independent `D₁₄`
actions, and the four retained graph automorphism groups have the displayed
order.  The `atlasAdj` order clause records the same fact before
conjugating back by the two displayed matrices. -/
def fullGraphAutomorphismGroup_claim28909 : Prop :=
  (∀ i : Fin 4, ∀ σ : Equiv.Perm Square,
    graphAutomorphism (normalizedAdj i) σ ↔ wreathDihedral σ) ∧
  (∀ i : Fin 4,
    Nat.card {σ : Equiv.Perm Square //
      graphAutomorphism (normalizedAdj i) σ} = wreathOrder) ∧
  (∀ i : Fin 4,
    Nat.card {σ : Equiv.Perm Square //
      graphAutomorphism (atlasAdj i) σ} = wreathOrder) ∧
  wreathOrder = 531284060160

/-- Claim 28910: the normalized zero stabilizer is exactly the unrestricted
`(p, ε, b)` parameterization, and its order is `6! · 2⁷ · 7⁶`. -/
def zeroStabilizerNormalForm_claim28910 : Prop :=
  (∀ i : Fin 4, ∀ σ : Equiv.Perm Square,
    zeroFixingAutomorphism (normalizedAdj i) σ ↔
      zeroFixingNormalForm σ) ∧
  (∀ i : Fin 4,
    Nat.card {σ : Equiv.Perm Square //
      zeroFixingAutomorphism (normalizedAdj i) σ} =
      Nat.factorial 6 * 2 ^ 7 * 7 ^ 6) ∧
  Nat.factorial 6 * 2 ^ 7 * 7 ^ 6 = 10842531840

end MathlibPlus.Open.ResearchFormalization.BatchR1102
