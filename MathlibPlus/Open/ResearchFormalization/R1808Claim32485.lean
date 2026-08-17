import Mathlib
import MathlibPlus.Combinatorics.SymmetricFiveColorCayley

namespace MathlibPlus.Open.ResearchFormalization.R1808Claim32485

open Set

noncomputable section

abbrev Fiber := ZMod 4
abbrev Base := Fin 3 → ZMod 3
abbrev Vertex := Fiber × Base

/-- Ordinary additive Cayley adjacency on the fixed `C₄ × C₃³` carrier. -/
def cayleyAdj (S : Set Vertex) (x y : Vertex) : Prop :=
  y - x ∈ S

def inverseClosed (S : Set Vertex) : Prop :=
  ∀ x : Vertex, x ∈ S ↔ -x ∈ S

def graphAutomorphism (S : Set Vertex) (p : Equiv.Perm Vertex) : Prop :=
  ∀ x y : Vertex,
    cayleyAdj S x y ↔ cayleyAdj S (p x) (p y)

def regularGraphCopy (S : Set Vertex)
    (R : Subgroup (Equiv.Perm Vertex)) : Prop :=
  (∀ r : R, graphAutomorphism S r.1) ∧
    ∀ x y : Vertex, ∃! r : R, r.1 x = y

def preservesFiberBlocks
    (R : Subgroup (Equiv.Perm Vertex)) : Prop :=
  ∀ r : R, ∃ q : Equiv.Perm Base,
    ∀ a : Fiber, ∀ v : Base, (r.1 (a, v)).2 = q v

def translationCopy : Subgroup (Equiv.Perm Vertex) :=
  Subgroup.closure (Set.range (fun g : Vertex => Equiv.addRight g))

def normalizedTranslationCopy
    (R : Subgroup (Equiv.Perm Vertex)) : Prop :=
  R = translationCopy

def fiberForm
    (f : Equiv.Perm Vertex) (π : Base → Equiv.Perm Fiber)
    (q : Equiv.Perm Base) : Prop :=
  ∀ a : Fiber, ∀ v : Base,
    f (a, v) = (π v a, q v)

def regularCopyConjugator
    (R T : Subgroup (Equiv.Perm Vertex)) (f : Equiv.Perm Vertex) : Prop :=
  ∀ p : Equiv.Perm Vertex,
    p ∈ T ↔ f⁻¹ * p * f ∈ R

def fiberCycle : Equiv.Perm Fiber :=
  Equiv.addRight 1

def fiberCycleSet : Set (Equiv.Perm Fiber) :=
  Set.range (fun n : ℕ => fiberCycle ^ n)

def normalizesFiberCycle (p : Equiv.Perm Fiber) : Prop :=
  ∀ z : Equiv.Perm Fiber, z ∈ fiberCycleSet →
    p * z * p⁻¹ ∈ fiberCycleSet

def squareMismatch (π : Base → Equiv.Perm Fiber) : Prop :=
  ∃ v : Base, ¬ normalizesFiberCycle (π v)

def blockKernelSet (S : Set Vertex) : Set (Equiv.Perm Vertex) :=
  {k | graphAutomorphism S k ∧
    ∀ a : Fiber, ∀ v : Base, (k (a, v)).2 = v}

def fullFiberKernelEvaluation (S : Set Vertex) : Prop :=
  ∀ v : Base, ∀ p : Equiv.Perm Fiber,
    ∃ k : Equiv.Perm Vertex,
      k ∈ blockKernelSet S ∧
        ∀ a : Fiber, k (a, v) = (p a, v)

def fiberRelation (S : Set Vertex) (u v : Base) : Set (Fiber × Fiber) :=
  {p | cayleyAdj S (p.1, u) (p.2, v)}

def emptyRelation : Set (Fiber × Fiber) := ∅
def completeRelation : Set (Fiber × Fiber) := Set.univ
def equalityRelation : Set (Fiber × Fiber) := {p | p.1 = p.2}
def offEqualityRelation : Set (Fiber × Fiber) := {p | p.1 ≠ p.2}

def matchingRelation (d : Fiber) : Set (Fiber × Fiber) :=
  {p | p.2 = p.1 + d}

def matchingComplement (d : Fiber) : Set (Fiber × Fiber) :=
  {p | p.2 ≠ p.1 + d}

def matchingAtDifference (S : Set Vertex) (d : Base → Fiber)
    (u v : Base) : Prop :=
  fiberRelation S u v = matchingRelation (d (v - u)) ∨
    fiberRelation S u v = matchingComplement (d (v - u))

def allowedBlockRelations (S : Set Vertex) (d : Base → Fiber) : Prop :=
  ∀ u v : Base, u ≠ v →
    fiberRelation S u v = emptyRelation ∨
      fiberRelation S u v = completeRelation ∨
        matchingAtDifference S d u v

def matchingDifference (S : Set Vertex) (d : Base → Fiber)
    (w : Base) : Prop :=
  ∃ u : Base, matchingAtDifference S d u (u + w)

def coherentMatchingHolonomy (S : Set Vertex) (d : Base → Fiber) : Prop :=
  ∀ u w : Base, w ≠ 0 →
    matchingAtDifference S d u (u + w) →
      matchingAtDifference S d (u + w) (u + w + w) →
        matchingAtDifference S d (u + w + w) u →
          d w + d w + d w = 0

/-- The literal normalization supplied by the exponent-three matching step;
empty and complete relations remain separate alternatives. -/
def literalBlockRelations (S : Set Vertex) : Prop :=
  ∀ u v : Base, u ≠ v →
    fiberRelation S u v = emptyRelation ∨
      fiberRelation S u v = completeRelation ∨
        fiberRelation S u v = equalityRelation ∨
          fiberRelation S u v = offEqualityRelation

def withinBlockUniform (S : Set Vertex) : Prop :=
  ∃ b : Bool, ∀ u : Base,
    fiberRelation S u u = if b then offEqualityRelation else emptyRelation

def preservesFiberRelation (p : Equiv.Perm Fiber)
    (R : Set (Fiber × Fiber)) : Prop :=
  ∀ a b : Fiber, (a, b) ∈ R ↔ (p a, p b) ∈ R

def withinBlockPermutationInvariant (S : Set Vertex) : Prop :=
  ∀ u : Base, ∀ p : Equiv.Perm Fiber,
    preservesFiberRelation p (fiberRelation S u u)

/-- The quotient action is derived from the given regular copy, rather than
supplied as an unrelated arbitrary permutation set. -/
def inducedBaseCopy
    (R : Subgroup (Equiv.Perm Vertex)) : Set (Equiv.Perm Base) :=
  {q | ∃ r : R, ∀ a : Fiber, ∀ v : Base,
    (r.1 (a, v)).2 = q v}

def regularPermutationSet
    (Q : Set (Equiv.Perm Base)) : Prop :=
  ∀ u v : Base, ∃! q : Equiv.Perm Base, q ∈ Q ∧ q u = v

def quotientPreservesColor (Q : Set (Equiv.Perm Base))
    (c : Base → Fin 5) : Prop :=
  ∀ q ∈ Q, ∀ u v : Base,
    c (q v - q u) = c (v - u)

noncomputable def relationDegree
    (R : Set (Fiber × Fiber)) (a : Fiber) : ℕ :=
  Nat.card {b : Fiber // (a, b) ∈ R}

def relationColorRealization
    (S : Set Vertex) (c : Base → Fin 5) : Prop :=
  ∀ u v : Base, u ≠ v →
    (fiberRelation S u v = emptyRelation ↔ c (v - u) = 0) ∧
      (fiberRelation S u v = completeRelation ↔ c (v - u) = 4) ∧
        (fiberRelation S u v = equalityRelation ↔ c (v - u) = 1) ∧
          (fiberRelation S u v = offEqualityRelation ↔ c (v - u) = 3)

def blockValencies (S : Set Vertex) (c : Base → Fin 5) : Prop :=
  ∀ u v : Base, u ≠ v → ∀ a : Fiber,
    (c (v - u) = 0 ↔ relationDegree (fiberRelation S u v) a = 0) ∧
      (c (v - u) = 4 ↔ relationDegree (fiberRelation S u v) a = 4) ∧
        (c (v - u) = 1 ↔ relationDegree (fiberRelation S u v) a = 1) ∧
          (c (v - u) = 3 ↔ relationDegree (fiberRelation S u v) a = 3)

def quotientColorData
    (S : Set Vertex)
    (R T : Subgroup (Equiv.Perm Vertex))
    (c : Base → Fin 5) : Prop :=
  MathlibPlus.Combinatorics.SymmetricFiveColorCayley.isSymmetricFiveColorCayleyStructure c ∧
    Set.range c ⊆ ({0, 1, 3, 4} : Set (Fin 5)) ∧
      relationColorRealization S c ∧
        blockValencies S c ∧
          withinBlockUniform S ∧
            withinBlockPermutationInvariant S ∧
              regularPermutationSet (inducedBaseCopy R) ∧
                regularPermutationSet (inducedBaseCopy T) ∧
                  quotientPreservesColor (inducedBaseCopy R) c ∧
                    quotientPreservesColor (inducedBaseCopy T) c

/-- The full prior context for the quotient coloring, with actual regular
copies and the actual block relations of the Cayley graph. -/
def quotientContext
    (S : Set Vertex)
    (R T : Subgroup (Equiv.Perm Vertex))
    (f : Equiv.Perm Vertex)
    (π : Base → Equiv.Perm Fiber)
    (q : Equiv.Perm Base)
    (d : Base → Fiber) : Prop :=
  0 ∉ S ∧
    inverseClosed S ∧
    regularGraphCopy S R ∧
    regularGraphCopy S T ∧
    preservesFiberBlocks R ∧
    preservesFiberBlocks T ∧
    normalizedTranslationCopy R ∧
    fiberForm f π q ∧
    regularCopyConjugator R T f ∧
    squareMismatch π ∧
    fullFiberKernelEvaluation S ∧
    allowedBlockRelations S d ∧
    coherentMatchingHolonomy S d ∧
    literalBlockRelations S ∧
    withinBlockUniform S ∧
    withinBlockPermutationInvariant S

/-- Claim 32485: the actual inter-block relations define the common symmetric
at-most-five-color quotient relation, with colors `0,4,1,3`, uniform
within-block choice, distinguishing block valencies, and both derived regular
quotient copies preserving that relation. -/
def quotientIsAtMostFiveColorRelation_claim32485 : Prop :=
  ∀ (S : Set Vertex)
    (R T : Subgroup (Equiv.Perm Vertex))
    (f : Equiv.Perm Vertex)
    (π : Base → Equiv.Perm Fiber)
    (q : Equiv.Perm Base)
    (d : Base → Fiber),
    quotientContext S R T f π q d →
      ∃ c : Base → Fin 5, quotientColorData S R T c

end
end MathlibPlus.Open.ResearchFormalization.R1808Claim32485
