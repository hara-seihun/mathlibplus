import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R1808Claim32484

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

/-- A regular copy is a subgroup of the graph automorphism group acting
regularly on the full vertex set. -/
def regularGraphCopy (S : Set Vertex)
    (R : Subgroup (Equiv.Perm Vertex)) : Prop :=
  (∀ r : R, graphAutomorphism S r.1) ∧
    ∀ x y : Vertex, ∃! r : R, r.1 x = y

/-- Preservation of the common four-point fiber block system. -/
def preservesFiberBlocks
    (R : Subgroup (Equiv.Perm Vertex)) : Prop :=
  ∀ r : R, ∃ q : Equiv.Perm Base,
    ∀ a : Fiber, ∀ v : Base, (r.1 (a, v)).2 = q v

/-- The normalized translation copy of `C₄ × C₃³`. -/
def translationCopy : Subgroup (Equiv.Perm Vertex) :=
  Subgroup.closure (Set.range (fun g : Vertex => Equiv.addRight g))

def normalizedTranslationCopy
    (R : Subgroup (Equiv.Perm Vertex)) : Prop :=
  R = translationCopy

/-- The displayed regular-copy conjugator has the fiberwise form from the
source, with a local permutation of the natural four-point fiber. -/
def fiberForm
    (f : Equiv.Perm Vertex) (π : Base → Equiv.Perm Fiber)
    (q : Equiv.Perm Base) : Prop :=
  ∀ a : Fiber, ∀ v : Base,
    f (a, v) = (π v a, q v)

def regularCopyConjugator
    (R T : Subgroup (Equiv.Perm Vertex)) (f : Equiv.Perm Vertex) : Prop :=
  ∀ p : Equiv.Perm Vertex,
    p ∈ T ↔ f⁻¹ * p * f ∈ R

/-- The natural four-cycle and its cyclic subgroup as a concrete permutation
carrier. -/
def fiberCycle : Equiv.Perm Fiber :=
  Equiv.addRight 1

def fiberCycleSet : Set (Equiv.Perm Fiber) :=
  Set.range (fun n : ℕ => fiberCycle ^ n)

def normalizesFiberCycle (p : Equiv.Perm Fiber) : Prop :=
  ∀ z : Equiv.Perm Fiber, z ∈ fiberCycleSet →
    p * z * p⁻¹ ∈ fiberCycleSet

def squareMismatch (π : Base → Equiv.Perm Fiber) : Prop :=
  ∃ v : Base, ¬ normalizesFiberCycle (π v)

/-- The actual kernel of the graph action on the fiber block system. -/
def blockKernelSet (S : Set Vertex) : Set (Equiv.Perm Vertex) :=
  {k | graphAutomorphism S k ∧
    ∀ a : Fiber, ∀ v : Base, (k (a, v)).2 = v}

/-- Evaluation of that block kernel is all of `S₄` on every block. -/
def fullFiberKernelEvaluation (S : Set Vertex) : Prop :=
  ∀ v : Base, ∀ p : Equiv.Perm Fiber,
    ∃ k : Equiv.Perm Vertex,
      k ∈ blockKernelSet S ∧
        ∀ a : Fiber, k (a, v) = (p a, v)

/-- The four relation types between two fibers. -/
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

/-- Empty and complete relations remain available in the block-relation
classification; only the matching cases carry an exponent. -/
def allowedBlockRelations (S : Set Vertex) (d : Base → Fiber) : Prop :=
  ∀ u v : Base, u ≠ v →
    fiberRelation S u v = emptyRelation ∨
      fiberRelation S u v = completeRelation ∨
        matchingAtDifference S d u v

def matchingDifference (S : Set Vertex) (d : Base → Fiber)
    (w : Base) : Prop :=
  ∃ u : Base, matchingAtDifference S d u (u + w)

/-- Coherence on the actual matching triangles in the elementary ternary
base.  Empty and complete block relations impose no matching holonomy. -/
def coherentMatchingHolonomy (S : Set Vertex) (d : Base → Fiber) : Prop :=
  ∀ u w : Base, w ≠ 0 →
    matchingAtDifference S d u (u + w) →
      matchingAtDifference S d (u + w) (u + w + w) →
        matchingAtDifference S d (u + w + w) u →
          d w + d w + d w = 0

/-- The complete prior `C₄ × C₃³` regular-copy, block-kernel, and coherence
context for the exponent-three matching conclusion. -/
def matchingContext
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
    coherentMatchingHolonomy S d

/-- Claim 32484: after the square-mismatched `S₄` kernel and coherent
matching context is in place, every actual nonconstant matching has exponent
zero.  Empty and complete inter-block relations are not excluded. -/
def exponentThreeForcesLiteralMatchings_claim32484 : Prop :=
  ∀ (S : Set Vertex)
    (R T : Subgroup (Equiv.Perm Vertex))
    (f : Equiv.Perm Vertex)
    (π : Base → Equiv.Perm Fiber)
    (q : Equiv.Perm Base)
    (d : Base → Fiber),
    matchingContext S R T f π q d →
      (∀ w : Base, w ≠ 0 → matchingDifference S d w →
        d w + d w + d w = 0 ∧ d w = 0) ∧
      (∀ u v : Base, u ≠ v →
        (fiberRelation S u v = matchingRelation (d (v - u)) →
          d (v - u) = 0 ∧ fiberRelation S u v = equalityRelation) ∧
        (fiberRelation S u v = matchingComplement (d (v - u)) →
          d (v - u) = 0 ∧ fiberRelation S u v = offEqualityRelation))

end
end MathlibPlus.Open.ResearchFormalization.R1808Claim32484
