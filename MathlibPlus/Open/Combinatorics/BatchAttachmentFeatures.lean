import Mathlib

namespace MathlibPlus.Open.Combinatorics

open scoped BigOperators

noncomputable section

abbrev AttachmentFeatures := ℕ × ℕ × ℕ × ℕ

def incidentBranchRoots {V : Type*} [Fintype V]
    (C : SimpleGraph V) (v : V) : Finset V := by
  classical
  letI := Fintype.ofFinite (C.neighborSet v)
  exact C.neighborFinset v

def finiteTreeDegree {V : Type*} [Fintype V]
    (C : SimpleGraph V) (v : V) : ℕ := by
  classical
  letI := Fintype.ofFinite (C.neighborSet v)
  exact C.degree v

def branchRootLoad {V : Type*} [Fintype V]
    (C : SimpleGraph V) (v r : V) : ℕ := by
  classical
  letI := Fintype.ofFinite (C.neighborSet r)
  exact ((C.neighborFinset r).erase v).card

def ambientRootLoad {V : Type*} [Fintype V]
    (C : SimpleGraph V) (r : V) : ℕ :=
  finiteTreeDegree C r - 1

def branchPairCount {V : Type*} [Fintype V]
    (roots : Finset V) : ℕ := by
  classical
  exact (roots.powerset.filter (fun pair => pair.card = 2)).card

def twoStepChannel {V : Type*} [Fintype V]
    (C : SimpleGraph V) (v : V) : ℕ := by
  classical
  let roots := incidentBranchRoots C v
  exact ∑ r ∈ roots, branchRootLoad C v r

def attachmentFeatures {V : Type*} [Fintype V]
    (C : SimpleGraph V) (v : V) : AttachmentFeatures := by
  classical
  let roots := incidentBranchRoots C v
  exact (1, roots.card, branchPairCount roots, twoStepChannel C v)

def fourSecondLeafAttachmentFeatures : Prop :=
  ∀ {V : Type*} [Fintype V] (C : SimpleGraph V) (v : V),
    C.IsTree →
      let roots := incidentBranchRoots C v
      let m := finiteTreeDegree C v
      attachmentFeatures C v =
        (1, m, Nat.choose m 2,
          ∑ r ∈ roots, ambientRootLoad C r)

end

end MathlibPlus.Open.Combinatorics
