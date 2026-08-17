import MathlibPlus.Open.GraphTheory.GraphCIQuotient

namespace MathlibPlus.Open.GraphTheory.QuotientConnectionLiftClaims28344

open scoped Pointwise

/-- The independent-fibre pullback of a quotient connection set. -/
def quotientOpenLift {G : Type*} [Group G]
    (N : Subgroup G) [N.Normal] (S : Set (G ⧸ N)) : Set G :=
  (QuotientGroup.mk' N) ⁻¹' S

/-- The complete-fibre pullback, with the identity removed for a simple graph. -/
def quotientClosedLift {G : Type*} [Group G]
    (N : Subgroup G) [N.Normal] (S : Set (G ⧸ N)) : Set G :=
  ((QuotientGroup.mk' N) ⁻¹' insert 1 S) \ {1}

/-- A set is a union of the left cosets of the normal subgroup `N`. -/
def leftNormalCosetUnion {G : Type*} [Group G]
    (N : Subgroup G) (U : Set G) : Prop :=
  ∀ n : G, n ∈ N → (fun x : G => n * x) '' U = U

/-- The identity-adjoined closed lift is a union of the normal-subgroup fibres. -/
def completeFiberNormalCosetUnion {G : Type*} [Group G]
    (N : Subgroup G) (U : Set G) : Prop :=
  ∀ n : G, n ∈ N →
    (fun x : G => n * x) '' insert 1 U = insert 1 U

/--
Claim 28344: quotient connection sets lift to the two ambient Cayley objects
associated with an independent or a complete normal-subgroup fibre, and a
quotient graph isomorphism lifts in both cases.
-/
def claim28344 : Prop :=
  ∀ (G : Type*) [Finite G] [Group G]
    (N : Subgroup G) [N.Normal]
    (S T : Set (G ⧸ N)),
    S = S⁻¹ → T = T⁻¹ → 1 ∉ S → 1 ∉ T →
    Nonempty (SimpleGraph.mulCayley S ≃g SimpleGraph.mulCayley T) →
    leftNormalCosetUnion N (quotientOpenLift N S) ∧
    leftNormalCosetUnion N (quotientOpenLift N T) ∧
    completeFiberNormalCosetUnion N (quotientClosedLift N S) ∧
    completeFiberNormalCosetUnion N (quotientClosedLift N T) ∧
    quotientOpenLift N S ∩ (N : Set G) = ∅ ∧
    quotientOpenLift N T ∩ (N : Set G) = ∅ ∧
    quotientClosedLift N S ∩ (N : Set G) = (N : Set G) \ {1} ∧
    quotientClosedLift N T ∩ (N : Set G) = (N : Set G) \ {1} ∧
    Nonempty (SimpleGraph.mulCayley (quotientOpenLift N S) ≃g
      SimpleGraph.mulCayley (quotientOpenLift N T)) ∧
    Nonempty (SimpleGraph.mulCayley (quotientClosedLift N S) ≃g
      SimpleGraph.mulCayley (quotientClosedLift N T))

end MathlibPlus.Open.GraphTheory.QuotientConnectionLiftClaims28344
