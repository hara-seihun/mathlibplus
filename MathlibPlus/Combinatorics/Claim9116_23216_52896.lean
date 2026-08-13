import MathlibPlus.Basic

open scoped BigOperators

namespace MathlibPlus.Combinatorics

namespace Claim9116

/-- An extended card isomorphism is involutive when its square is the identity. -/
def involutiveCardMap {α : Type*} (e : α ≃ α) : Prop :=
  e.trans e = Equiv.refl α

/-- Every selected card map is involutive.  The carrier is the retained/full
vertex set after the packet's extension convention has been fixed. -/
def selectedCardMapsInvolutive {ι α : Type*} (maps : ι → α ≃ α) : Prop :=
  ∀ i, involutiveCardMap (maps i)

end Claim9116

namespace Claim23216

/-- Count ordered distinct triples by the isomorphism classes of their deleted
cards.  `cardType` is the supplied class of `G - v`; the graph-deletion API is
not rebuilt here because the source packet only specifies the class relation. -/
noncomputable def orderedDistinctTripleCardCount
    {V C : Type*} [Fintype V] [DecidableEq V]
    (cardType : V → C) (F H K : C) : ℕ := by
  classical
  exact (Finset.univ.filter (fun t : V × (V × V) =>
    t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2 ∧ t.2.1 ≠ t.2.2 ∧
      cardType t.1 = F ∧ cardType t.2.1 = H ∧ cardType t.2.2 = K)).card

end Claim23216

namespace Claim52896

/-- The rooted-orbit quotient graph is required to be a tree. -/
def rootedOrbitQuotientIsTree {Q : Type*} (quotientGraph : SimpleGraph Q) : Prop :=
  quotientGraph.IsTree

/-- An integral signed multiplicity has total mass zero. -/
def balancedSignedMultiplicity {V : Type*} [Fintype V]
    (μ : V → ℤ) : Prop :=
  ∑ v, μ v = 0

/-- Total positive packet mass of an integral signed multiplicity. -/
def positivePacketMass {V : Type*} [Fintype V] (μ : V → ℤ) : ℤ :=
  ∑ v, max (μ v) 0

/-- Total negative packet mass, written as a positive integer mass. -/
def negativePacketMass {V : Type*} [Fintype V] (μ : V → ℤ) : ℤ :=
  ∑ v, max (-μ v) 0

/-- Zero total signed mass gives equal positive and negative packet masses. -/
theorem positivePacketMass_eq_negativePacketMass
    {V : Type*} [Fintype V] (μ : V → ℤ)
    (hμ : balancedSignedMultiplicity μ) :
    positivePacketMass μ = negativePacketMass μ := by
  have hpoint (v : V) :
      μ v = max (μ v) 0 - max (-μ v) 0 := by
    omega
  have hsum :
      (∑ v, μ v) = positivePacketMass μ - negativePacketMass μ := by
    change (∑ v, μ v) =
      (∑ v, max (μ v) 0) - (∑ v, max (-μ v) 0)
    calc
      (∑ v, μ v) = ∑ v, (max (μ v) 0 - max (-μ v) 0) := by
        apply Finset.sum_congr rfl
        intro v hv
        exact hpoint v
      _ = (∑ v, max (μ v) 0) - (∑ v, max (-μ v) 0) := by
        rw [Finset.sum_sub_distrib]
  rw [hμ] at hsum
  omega

end Claim52896

end MathlibPlus.Combinatorics
