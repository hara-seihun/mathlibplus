import Mathlib

namespace MathlibPlus.Open.CompleteGraphDual

/-- The ground coordinates in the complete-graph-dual family: two-element
subsets of the vertex set `Fin M`. -/
def edgeGround (M : ℕ) : Finset (Finset (Fin M)) :=
  Finset.powersetCard 2 (Finset.univ : Finset (Fin M))

/-- The member indexed by vertex `i`: all ground edges incident with `i`. -/
def edgeStar (M : ℕ) (i : Fin M) : Finset (Finset (Fin M)) :=
  (edgeGround M).filter (fun e => i ∈ e)

/-- The indexed complete-graph-dual family. -/
def edgeFamily (M : ℕ) : Finset (Finset (Finset (Fin M))) :=
  Finset.univ.image (edgeStar M)

/--
Claim 34724.  For every `M ≥ 4`, the complete-graph-dual family has `M`
distinct members, each of size `M - 1`, and every ground coordinate has
degree two.
-/
def claim34724 : Prop :=
  ∀ M : ℕ, 4 ≤ M →
    Function.Injective (edgeStar M) ∧
      (edgeFamily M).card = M ∧
      (∀ i : Fin M, (edgeStar M i).card = M - 1) ∧
      (∀ e ∈ edgeGround M,
        (Finset.univ.filter (fun i : Fin M => e ∈ edgeStar M i)).card = 2)

namespace SunflowerProduct

/-- Uniformity of a finite family of finite sets. -/
def UniformFamily {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) : Prop :=
  ∃ k : ℕ, ∀ A ∈ family, A.card = k

/-- A three-sunflower is a triple of distinct members with equal pairwise
intersections. -/
def ThreeSunflowerFree {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) : Prop :=
  ∀ ⦃A B C : Finset α⦄,
    A ∈ family → B ∈ family → C ∈ family →
    A ≠ B → A ≠ C → B ≠ C →
    ¬ (A ∩ B = A ∩ C ∧ A ∩ B = B ∩ C)

/-- Embed a finite set from the left ground set into the disjoint sum. -/
def liftLeft {α β : Type*} [DecidableEq α] [DecidableEq β]
    (A : Finset α) : Finset (α ⊕ β) :=
  A.image Sum.inl

/-- Embed a finite set from the right ground set into the disjoint sum. -/
def liftRight {α β : Type*} [DecidableEq α] [DecidableEq β]
    (B : Finset β) : Finset (α ⊕ β) :=
  B.image Sum.inr

/-- Direct product of families on disjoint ground sets. -/
def productFamily {α β : Type*} [DecidableEq α] [DecidableEq β]
    (familyA : Finset (Finset α)) (familyB : Finset (Finset β)) :
    Finset (Finset (α ⊕ β)) :=
  (familyA.product familyB).image
    (fun pair => liftLeft pair.1 ∪ liftRight pair.2)

/--
Claim 34728.  The direct product of uniform 3-sunflower-free families on
disjoint ground sets is again 3-sunflower-free.
-/
def claim34728 : Prop :=
  ∀ (α β : Type*) [DecidableEq α] [DecidableEq β]
    (familyA : Finset (Finset α)) (familyB : Finset (Finset β)),
    UniformFamily familyA → ThreeSunflowerFree familyA →
    UniformFamily familyB → ThreeSunflowerFree familyB →
    ThreeSunflowerFree (productFamily familyA familyB)

end SunflowerProduct

end MathlibPlus.Open.CompleteGraphDual
