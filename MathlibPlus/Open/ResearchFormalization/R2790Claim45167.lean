import MathlibPlus.Open.ResearchFormalization.R2790Claims45165_45166

open scoped BigOperators
open Classical

namespace MathlibPlus.Open.ResearchFormalization.R2790

noncomputable section

/-- Monic irreducibility of every rooted boundary atom in an occurrence
multiset. -/
def monicIrreducibleBoundaryAtoms45167
    (M : BranchMultiset) (u v : TreePolynomial) : Prop :=
  ∀ R ∈ M,
    Polynomial.Monic (branchB R u v) ∧
      Irreducible (branchB R u v)

/-- Distinct rooted-tree occurrences have distinct rooted boundary atoms. -/
def distinctBoundaryAtoms45167
    (M : BranchMultiset) (u v : TreePolynomial) : Prop :=
  ∀ R ∈ M, ∀ S ∈ M, R ≠ S →
    branchB R u v ≠ branchB S u v

def zeroAdditiveResidual45167
    (E F : BranchMultiset) (u v : TreePolynomial) : Prop :=
  branchSum E u v = branchSum F u v

def canonicalResidualEquation45167
    (C E F : BranchMultiset) (u v : TreePolynomial) : Prop :=
  branchProduct C u v *
      (branchProduct E u v - branchProduct F u v) =
    branchSum F u v - branchSum E u v

/-- Zero additive residual cancels the common product in the exact residual
 equation, and unique factorization then recovers the actual branch
 occurrence multiset, including multiplicity. -/
def claim45167 : Prop :=
  ∀ (C E F : BranchList) (u v : TreePolynomial),
    minimumEqualUCandidate (C ++ E) u v →
      minimumEqualUCandidate (C ++ F) u v →
        nodeU (C ++ E) u v = nodeU (C ++ F) u v →
          let CM : BranchMultiset := Multiset.ofList C
          let EM : BranchMultiset := Multiset.ofList E
          let FM : BranchMultiset := Multiset.ofList F
          monicIrreducibleBoundaryAtoms45167 (CM + EM + FM) u v →
            distinctBoundaryAtoms45167 (CM + EM + FM) u v →
              canonicalResidualEquation45167 CM EM FM u v →
                (zeroAdditiveResidual45167 EM FM u v →
                  branchProduct EM u v = branchProduct FM u v ∧
                    EM = FM) ∧
                  (EM ≠ FM → ¬ zeroAdditiveResidual45167 EM FM u v)

end

end MathlibPlus.Open.ResearchFormalization.R2790
