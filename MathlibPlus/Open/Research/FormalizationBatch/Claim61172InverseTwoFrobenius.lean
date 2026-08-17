import Mathlib
import MathlibPlus.Open.GraphTheory.HalfSupportInversePairIncidenceRigidity

noncomputable section

namespace MathlibPlus.Open.Research.F3Rank6_7InverseTwoFrobenius

open MathlibPlus.Open.GraphTheory

abbrev F3 := ZMod 3
abbrev FPolynomial := Polynomial F3

def modulus : FPolynomial :=
  Polynomial.X ^ 6 + Polynomial.X + Polynomial.C 2

abbrev F := FPolynomial ⧸ Ideal.span ({modulus} : Set FPolynomial)

def inversePower (x : F) : F := x ^ 727

def q (c d : F) (x : F) : F :=
  let _ := Classical.decEq F
  if x = 0 then 0 else inversePower x + c * x + d * x ^ 3

def fieldModel : Prop :=
  ∀ x : F, x ≠ 0 →
    x * x ^ 727 = 1 ∧ x ^ 727 * x = 1

def coefficientPermutationClassification : Prop :=
  ∀ c d : F, Function.Bijective (q c d) ↔ (c, d) = (0, 0)

def additiveGroupModel : Prop :=
  Nonempty (F ≃+ (Fin 6 → F3))

abbrev inverseAtomVertex :=
  Sum (inversePairAtom F) (inversePairAtom F)

def atomDifferenceIncidence (r : F → F)
    (D E : inversePairAtom F) : Prop :=
  ∃ a b x : F,
    (D.1 : Set F) = ({a, -a} : Set F) ∧
      (E.1 : Set F) = ({b, -b} : Set F) ∧
        r (x + a) - r x ∈ ({b, -b} : Set F)

def incidenceAdjacency (r : F → F)
    (u v : inverseAtomVertex) : Prop :=
  match u, v with
  | Sum.inl D, Sum.inr E => atomDifferenceIncidence r D E
  | Sum.inr E, Sum.inl D => atomDifferenceIncidence r D E
  | _, _ => False

def incidenceConnected (r : F → F)
    (u v : inverseAtomVertex) : Prop :=
  Relation.ReflTransGen (incidenceAdjacency r) u v

def connectedIncidenceGraph (r : F → F) : Prop :=
  ∀ u v : inverseAtomVertex, incidenceConnected r u v

def componentUnion (r : F → F)
    (I : Set inverseAtomVertex) : Prop :=
  ∀ u v : inverseAtomVertex, incidenceConnected r u v →
    (u ∈ I ↔ v ∈ I)

def sourceAtoms (I : Set inverseAtomVertex) : Set (inversePairAtom F) :=
  {D | Sum.inl D ∈ I}

def targetAtoms (I : Set inverseAtomVertex) : Set (inversePairAtom F) :=
  {D | Sum.inr D ∈ I}

def connectionSetOfAtoms
    (A : Set (inversePairAtom F)) : Set F :=
  {d | ∃ D, D ∈ A ∧ d ∈ inversePairAtomDirections D}

def sourceConnectionSet (I : Set inverseAtomVertex) : Set F :=
  connectionSetOfAtoms (sourceAtoms I)

def targetConnectionSet (I : Set inverseAtomVertex) : Set F :=
  connectionSetOfAtoms (targetAtoms I)

def identityFree (S : Set F) : Prop :=
  (0 : F) ∉ S

def inverseClosed (S : Set F) : Prop :=
  ∀ ⦃x : F⦄, x ∈ S → -x ∈ S

def additiveCayleyRelation (S : Set F) (x y : F) : Prop :=
  y - x ∈ S

def cayleyTransport (r : F → F) (S T : Set F) : Prop :=
  Function.Bijective r ∧
    ∀ x y : F,
      additiveCayleyRelation S x y ↔
        additiveCayleyRelation T (r x) (r y)

def ordinaryUndirectedCayleyCIDefect
    (r : F → F) (S T : Set F) : Prop :=
  identityFree S ∧
    identityFree T ∧
    inverseClosed S ∧
    inverseClosed T ∧
    cayleyTransport r S T ∧
    ¬ ∃ e : F ≃+ F, e '' S = T

def finiteScope : Prop :=
  Set.ncard (Set.univ : Set F) = 729 ∧
    Set.ncard (Set.univ : Set (F × F)) = 531441 ∧
    Set.ncard (Set.univ : Set (inversePairAtom F)) = 364 ∧
    Set.ncard (Set.univ : Set (inversePairAtom F × F)) = 265356

def componentUnionConsequence (r : F → F) : Prop :=
  ∀ I : Set inverseAtomVertex,
    componentUnion r I →
      let S := sourceConnectionSet I
      let T := targetConnectionSet I
      (S = ∅ ∨ S = ({0} : Set F)ᶜ) ∧
        (T = ∅ ∨ T = ({0} : Set F)ᶜ) ∧
        S = T ∧
        cayleyTransport r S T ∧
        Set.image (AddEquiv.refl F) S = T ∧
        ¬ ordinaryUndirectedCayleyCIDefect r S T

def noFamilyComponentUnionDefect : Prop :=
  ∀ c d : F, Function.Bijective (q c d) →
    componentUnionConsequence (q c d)

def claim61172 : Prop :=
  fieldModel ∧
    finiteScope ∧
    coefficientPermutationClassification ∧
    additiveGroupModel ∧
    Function.Bijective (q 0 0) ∧
    connectedIncidenceGraph (q 0 0) ∧
    componentUnionConsequence (q 0 0) ∧
    noFamilyComponentUnionDefect

end MathlibPlus.Open.Research.F3Rank6_7InverseTwoFrobenius

end
