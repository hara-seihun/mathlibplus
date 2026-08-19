import MathlibPlus.Open.ResearchFormalization.R1808Claim32484

namespace MathlibPlus.Open.ResearchFormalization.R1808Claim32481Repair

open MathlibPlus.Open.ResearchFormalization.R1808Claim32484

noncomputable section

/-- The natural and transported regular cyclic four-subgroups on one fiber. -/
def naturalC4 : Subgroup (Equiv.Perm Fiber) :=
  Subgroup.closure ({fiberCycle} : Set (Equiv.Perm Fiber))

def transportedC4 (p : Equiv.Perm Fiber) : Subgroup (Equiv.Perm Fiber) :=
  Subgroup.closure ({p⁻¹ * fiberCycle * p} : Set (Equiv.Perm Fiber))

def localGeneratedC4Pair (p : Equiv.Perm Fiber) :
    Subgroup (Equiv.Perm Fiber) :=
  Subgroup.closure
    ((naturalC4 : Set (Equiv.Perm Fiber)) ∪
      (transportedC4 p : Set (Equiv.Perm Fiber)))

def localSquareHolonomy (p : Equiv.Perm Fiber) :
    Subgroup (Equiv.Perm Fiber) :=
  Subgroup.closure
    ({fiberCycle ^ 2, p⁻¹ * fiberCycle ^ 2 * p} : Set (Equiv.Perm Fiber))

def regularKleinFour (K : Subgroup (Equiv.Perm Fiber)) : Prop :=
  Nat.card K = 4 ∧
    ∀ x y : Fiber, ∃! k : K, (k : Equiv.Perm Fiber) x = y

def localMismatchedPair (p : Equiv.Perm Fiber) : Prop :=
  naturalC4 ≠ transportedC4 p

/-- The graph context with the kernel-evaluation conclusion removed from its
hypotheses, so the saturation assertion is not a restatement of an assumed
full-fiber evaluation predicate. -/
def mismatchedKernelContext
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
    allowedBlockRelations S d ∧
    coherentMatchingHolonomy S d

/-- Claim 32481: every mismatched local pair generates the full fiber
symmetric group, its two squares generate a regular Klein four subgroup, and
the actual block kernel evaluates to every fiber permutation on every block. -/
def claim32481 : Prop :=
  ∀ (S : Set Vertex)
    (R T : Subgroup (Equiv.Perm Vertex))
    (f : Equiv.Perm Vertex)
    (π : Base → Equiv.Perm Fiber)
    (q : Equiv.Perm Base)
    (d : Base → Fiber),
    mismatchedKernelContext S R T f π q d →
      (∀ v : Base, localMismatchedPair (π v) →
        localGeneratedC4Pair (π v) = ⊤ ∧
          regularKleinFour (localSquareHolonomy (π v))) ∧
      fullFiberKernelEvaluation S

end

end MathlibPlus.Open.ResearchFormalization.R1808Claim32481Repair
