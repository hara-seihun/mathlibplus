import Mathlib
import MathlibPlus.Algebra.FamilyProduct
import MathlibPlus.Open.NewResearch2.R0316Repair

namespace MathlibPlus.Open.NewResearch2.R0316

noncomputable section

abbrev Core := Sum (Fin 3) (Fin 3)

def tCoordinate (i : Fin 3) : Core := Sum.inl i

def zCoordinate (i : Fin 3) : Core := Sum.inr i

def tCoordinates : Set Core := Set.range tCoordinate

def zCoordinates : Set Core := Set.range zCoordinate

def cubeFamily (U : Set Core) : Set (Set Core) :=
  {A | A ⊆ U}

/-- The empty union and the seven nonempty unions of the generators
`Z ∪ {t_i}`. -/
def baseType : Set (Set Core) :=
  {A | A = ∅ ∨
    ∃ S : Set Core, S ⊆ tCoordinates ∧ S.Nonempty ∧
      A = zCoordinates ∪ S}

def fullType : Set (Set Core) := cubeFamily (Set.univ : Set Core)

def puncturedType (x : Core) : Set (Set Core) :=
  MathlibPlus.Algebra.FamilyProduct.familyProduct baseType
    (cubeFamily (Set.univ \ {x}))

def allowedInnerType (B : Set (Set Core)) : Prop :=
  B = baseType ∨
    (∃ x : Core, B = puncturedType x) ∨
      B = fullType

def fiberJoin (A B : Set (Set Core)) : Set (Set Core) :=
  MathlibPlus.Algebra.FamilyProduct.familyProduct A B

def joinExpansionCost (A B : Set (Set Core)) : ℕ :=
  Set.ncard (fiberJoin A B)

def allowedTraceCoupledFiberSystem
    {Y : Type*} [Fintype Y]
    (support : Set (Set Y))
    (fiber : Set Y → Set (Set Core)) : Prop :=
  MathlibPlus.Open.NewResearch2.R0316Repair.claim19739_traceCoupledFiberSystem
      support fiber ∧
    ∀ S : Set Y, S ∈ support → allowedInnerType (fiber S)

/-- Claim 19747: the exact seven-type multiplication table on the six-coordinate
core.  The base contains the empty union as well as the seven nonempty
unions of `Z ∪ {t_i}`. -/
def claim19747_exactSevenTypeMultiplicationTable : Prop :=
  fiberJoin baseType baseType = baseType ∧
    (∀ x : Core,
      fiberJoin baseType (puncturedType x) = puncturedType x) ∧
    (∀ x : Core,
      fiberJoin (puncturedType x) (puncturedType x) = puncturedType x) ∧
    (∀ x y : Core, x ≠ y →
      fiberJoin (puncturedType x) (puncturedType y) = fullType) ∧
    (∀ B : Set (Set Core), allowedInnerType B →
      fiberJoin fullType B = fullType)

/-- Claim 19746: in the supplied trace-coupled system whose fibers use the
seven allowed types, the join entry is the exact family product, its cost is
its cardinality, and coupling gives the forced allowed target and the
cardinality lower bound at trace union. -/
def claim19746_fiberJoinTableAndJoinExpansionCost : Prop :=
  ∀ {Y : Type*} [Fintype Y]
    (support : Set (Set Y))
    (fiber : Set Y → Set (Set Core)),
    allowedTraceCoupledFiberSystem support fiber →
      (∀ A B : Set (Set Core),
        allowedInnerType A → allowedInnerType B →
          fiberJoin A B =
              MathlibPlus.Algebra.FamilyProduct.familyProduct A B ∧
            joinExpansionCost A B = Set.ncard (fiberJoin A B) ∧
            allowedInnerType (fiberJoin A B)) ∧
      (∀ S T : Set Y, S ∈ support → T ∈ support →
        fiberJoin (fiber S) (fiber T) ⊆ fiber (S ∪ T) ∧
          joinExpansionCost (fiber S) (fiber T) ≤
            Set.ncard (fiber (S ∪ T)))

end

end MathlibPlus.Open.NewResearch2.R0316
