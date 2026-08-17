import Mathlib
import MathlibPlus.Open.ResearchFormalization.CyclicSevenSquared

noncomputable section

namespace MathlibPlus.Open.ResearchFormalization.R0990

open MathlibPlus.Open.ResearchFormalization.CyclicSevenSquared

/-- The inverse-pair atom represented by a nonzero vector. -/
def inversePairAtom (v : V7) : Finset V7 :=
  {v, -v}

/-- The actual inverse-pair atoms on the nonzero vectors of `V7`. -/
def inversePairAtomPredicate (S : Finset V7) : Prop :=
  ∃ v : V7, v ≠ 0 ∧ S = inversePairAtom v

def inversePairAtoms : Set (Finset V7) :=
  {S | inversePairAtomPredicate S}

/-- A one-dimensional projective line in the actual `V7` vector space. -/
def projectiveLinePredicate (L : Submodule (ZMod 7) V7) : Prop :=
  L ≠ ⊥ ∧ L ≠ ⊤ ∧ Set.ncard (L : Set V7) = 7

def projectiveLines : Set (Submodule (ZMod 7) V7) :=
  {L | projectiveLinePredicate L}

/-- Incidence of an inverse-pair atom with a projective line. -/
def atomOnProjectiveLine
    (L : Submodule (ZMod 7) V7) (S : Finset V7) : Prop :=
  ∀ v : V7, v ∈ S → v ∈ L

def atomsOnProjectiveLine
    (L : Submodule (ZMod 7) V7) : Set (Finset V7) :=
  {S | inversePairAtomPredicate S ∧ atomOnProjectiveLine L S}

/-- The graph of the concrete `GL(2,7)` action on the actual inverse-pair
atom carrier. -/
def atomActionGraph (M : GL2_7) : Set (Finset V7 × Finset V7) :=
  {q |
    inversePairAtomPredicate q.1 ∧
      inversePairAtomPredicate q.2 ∧ glImage M q.1 = q.2}

/-- The image of `GL(2,7)` in its action on inverse-pair atoms. -/
def effectiveAtomActionImage : Set (Set (Finset V7 × Finset V7)) :=
  Set.range atomActionGraph

/-- The kernel predicate for the concrete action on every actual atom. -/
def atomActionKernel (M : GL2_7) : Prop :=
  ∀ S : Finset V7, inversePairAtomPredicate S → glImage M S = S

/-- The negative identity element of the concrete general linear group. -/
def negIdentity : GL2_7 :=
  -(1 : GL2_7)

/-- Claim 27995: the 24 inverse-pair atoms form three atoms on each of the
 eight projective lines, and the concrete `GL(2,7)` atom action has kernel
 `{±I}` and effective order `1008`. -/
def effectiveGL2SevenAtomAction_claim27995 : Prop :=
  Set.ncard inversePairAtoms = 24 ∧
    Set.ncard projectiveLines = 8 ∧
    (∀ L : Submodule (ZMod 7) V7,
      L ∈ projectiveLines → Set.ncard (atomsOnProjectiveLine L) = 3) ∧
    (∀ S : Finset V7,
      S ∈ inversePairAtoms →
        ∃! L : Submodule (ZMod 7) V7,
          L ∈ projectiveLines ∧ atomOnProjectiveLine L S) ∧
    Fintype.card GL2_7 = 2016 ∧
    (∀ M : GL2_7,
      atomActionKernel M ↔
        M = (1 : GL2_7) ∨ M = negIdentity) ∧
    Set.ncard effectiveAtomActionImage = 1008

end MathlibPlus.Open.ResearchFormalization.R0990
