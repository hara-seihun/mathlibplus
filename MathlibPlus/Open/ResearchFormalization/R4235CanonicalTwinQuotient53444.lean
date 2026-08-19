import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R4235CanonicalTwinQuotient53444

open scoped Pointwise

noncomputable section

/-- The closed- and open-neighborhood twin periods, written as the exact
setwise left stabilizers of the connection set. -/
def trueTwinPeriod {G : Type*} [CommGroup G] (S : Set G) : Subgroup G :=
  MulAction.stabilizer G (insert 1 S)

def falseTwinPeriod {G : Type*} [CommGroup G] (S : Set G) : Subgroup G :=
  MulAction.stabilizer G S

/-- The quotient coordinate attached to a period subgroup. -/
def quotientCoordinate {G : Type*} [CommGroup G]
    (P : Subgroup G) (x : G) : G ⧸ P :=
  QuotientGroup.mk' P x

/-- The canonical fibre over a quotient vertex. -/
abbrev canonicalFibre {G : Type*} [CommGroup G]
    (P : Subgroup G) (q : G ⧸ P) :=
  {x : G // quotientCoordinate P x = q}

/-- The loopless quotient connection set is the image of the original
connection set with its quotient identity removed. -/
def quotientConnectionSet {G : Type*} [CommGroup G]
    (P : Subgroup G) (S : Set G) : Set (G ⧸ P) :=
  Set.image (QuotientGroup.mk' P) S \ ({1} : Set (G ⧸ P))

/-- Twin-freeness in the open-neighborhood convention. -/
def openTwinFree {V : Type*} (graph : SimpleGraph V) : Prop :=
  ∀ q q', (∀ z, graph.Adj q z ↔ graph.Adj q' z) → q = q'

/-- Twin-freeness in the closed-neighborhood convention. -/
def closedTwinFree {V : Type*} (graph : SimpleGraph V) : Prop :=
  ∀ q q',
    (∀ z, (z = q ∨ graph.Adj q z) ↔
      (z = q' ∨ graph.Adj q' z)) → q = q'

/-- The complete-fibre blow-up over the exact quotient Cayley graph. -/
def completeFibreBlowup {G : Type*} [CommGroup G]
    (P : Subgroup G) (Sbar : Set (G ⧸ P)) (graph : SimpleGraph G) : Prop :=
  (1 : G ⧸ P) ∉ Sbar ∧
    Sbar = Sbar⁻¹ ∧
    closedTwinFree (SimpleGraph.mulCayley Sbar) ∧
    (∀ x y : G,
      graph.Adj x y ↔
        ((quotientCoordinate P x = quotientCoordinate P y ∧ x ≠ y) ∨
          (SimpleGraph.mulCayley Sbar).Adj
            (quotientCoordinate P x) (quotientCoordinate P y)))

/-- The independent-fibre blow-up over the exact quotient Cayley graph. -/
def independentFibreBlowup {G : Type*} [CommGroup G]
    (P : Subgroup G) (Sbar : Set (G ⧸ P)) (graph : SimpleGraph G) : Prop :=
  (1 : G ⧸ P) ∉ Sbar ∧
    Sbar = Sbar⁻¹ ∧
    openTwinFree (SimpleGraph.mulCayley Sbar) ∧
    (∀ x y : G,
      graph.Adj x y ↔
        (SimpleGraph.mulCayley Sbar).Adj
          (quotientCoordinate P x) (quotientCoordinate P y))

/-- A set is a union of the left cosets of a period subgroup. -/
def unionOfPeriodCosets {G : Type*} [CommGroup G]
    (P : Subgroup G) (U : Set G) : Prop :=
  ∀ x : G, x ∈ U → ∀ h : G, h ∈ (P : Set G) → h * x ∈ U

/--
S2 (claim 53444): each nontrivial canonical twin period gives the exact
quotient Cayley graph, canonical quotient fibres, and the corresponding
complete- or independent-fibre blow-up; the quotient is twin-free in the
same closed- or open-neighborhood convention.
-/
def claim53444 : Prop :=
  ∀ (G : Type*) [Fintype G] [CommGroup G] (S : Set G),
    S = S⁻¹ → 1 ∉ S →
      (trueTwinPeriod S ≠ ⊥ →
        unionOfPeriodCosets (trueTwinPeriod S) (insert 1 S) ∧
          completeFibreBlowup
            (trueTwinPeriod S)
            (quotientConnectionSet (trueTwinPeriod S) (insert 1 S))
            (SimpleGraph.mulCayley S)) ∧
      (falseTwinPeriod S ≠ ⊥ →
        unionOfPeriodCosets (falseTwinPeriod S) S ∧
          independentFibreBlowup
            (falseTwinPeriod S)
            (quotientConnectionSet (falseTwinPeriod S) S)
            (SimpleGraph.mulCayley S))

end

end MathlibPlus.Open.ResearchFormalization.R4235CanonicalTwinQuotient53444
