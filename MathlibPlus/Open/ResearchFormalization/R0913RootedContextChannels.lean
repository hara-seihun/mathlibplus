import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.R0913

noncomputable section
open Classical

/-- A finite rooted tree, with the list retaining its rooted branch topology. -/
inductive RootedTree where
  | node (branches : List RootedTree)

abbrev RootedContext := List RootedTree

mutual
  def rootedTreeSize : RootedTree → ℕ
    | .node branches => 1 + (branches.map rootedTreeSize).sum

  def rootedBranchDegree : RootedTree → ℕ
    | .node branches => branches.length
end

/-- The root degree of a context at the distinguished port. -/
def contextRootDegree (C : RootedContext) : ℕ := C.length

/-- The finite size of a rooted context. -/
def contextSize (C : RootedContext) : ℕ :=
  (C.map rootedTreeSize).sum

abbrev NatJet := ℕ × ℕ × ℕ
abbrev Jet (R : Type*) := R × R × R

def rootJetProductNat (j c : NatJet) : NatJet :=
  (j.1 + c.1, j.2.1 + c.2.1 + j.1 * c.1, j.2.2 + c.2.2)

/-- The aggregate D-0116 jet of the finite rooted branches at a port. -/
def aggregateJetNat (C : RootedContext) : NatJet :=
  C.foldl
    (fun j branch =>
      rootJetProductNat j (1, 0, rootedBranchDegree branch))
    (0, 0, 0)

def aggregateJet {R : Type*} [CommRing R] (C : RootedContext) : Jet R :=
  ((aggregateJetNat C).1,
    (aggregateJetNat C).2.1,
    (aggregateJetNat C).2.2)

def rootJetProduct {R : Type*} [CommRing R] (j c : Jet R) : Jet R :=
  (j.1 + c.1, j.2.1 + c.2.1 + j.1 * c.1, j.2.2 + c.2.2)

def graftedJet {R : Type*} [CommRing R] (j c : Jet R) : Jet R :=
  rootJetProduct j c

def augmentedFeature {R : Type*} [CommRing R] (j : Jet R) : Fin 4 → R :=
  ![1, j.1, j.2.1, j.2.2]

/-- The displayed lower-unitriangular context action. -/
def contextActionMatrix {R : Type*} [CommRing R]
    (c : Jet R) : Matrix (Fin 4) (Fin 4) R :=
  !![1, 0, 0, 0;
     c.1, 1, 0, 0;
     c.2.1, c.1, 1, 0;
     c.2.2, 0, 0, 1]

/-- A finite port-labelled local event family, recorded by its local jets. -/
def PortLabelledFamily (R E P : Type*) [CommRing R] :=
  E → P → Jet R

def familyFeatureMatrix {R E P : Type*} [CommRing R]
    (events : PortLabelledFamily R E P) (port : P) : Matrix (Fin 4) E R :=
  fun i e => augmentedFeature (events e port) i

/-- Attach one fixed context at the same distinguished port in every event. -/
def attachContextAtPort {R E P : Type*} [CommRing R] [DecidableEq P]
    (context : RootedContext) (events : PortLabelledFamily R E P)
    (distinguished : P) : PortLabelledFamily R E P :=
  fun e port =>
    if port = distinguished then
      graftedJet (events e port) (aggregateJet context)
    else events e port

def attachedFamilyFeatureMatrix {R E P : Type*} [CommRing R] [DecidableEq P]
    (context : RootedContext) (events : PortLabelledFamily R E P)
    (distinguished : P) : Matrix (Fin 4) E R :=
  familyFeatureMatrix (attachContextAtPort context events distinguished)
    distinguished

def localKernelCondition {R E : Type*} [CommRing R] [Fintype E]
    (A : Matrix (Fin 4) E R) (x : E → R) : Prop :=
  ∀ i : Fin 4, ∑ e : E, A i e * x e = 0

/-- Claim 25586: every finite rooted context acts through its aggregate jet at
one common distinguished port, preserving the local four-channel row span and
right kernel. -/
def claim25586 : Prop :=
  ∀ {R E P : Type*} [CommRing R] [CharZero R] [Fintype E] [Fintype P]
      [DecidableEq P] (context : RootedContext)
      (events : PortLabelledFamily R E P) (distinguished : P),
    let original := familyFeatureMatrix events distinguished
    let attached := attachedFamilyFeatureMatrix context events distinguished
    let U := contextActionMatrix (aggregateJet context)
    attached = U * original ∧
      U.IsLowerTriangular ∧
      (∀ i : Fin 4, U i i = 1) ∧
      U.det = 1 ∧
      Submodule.span R (Set.range (fun i : Fin 4 => attached i)) =
        Submodule.span R (Set.range (fun i : Fin 4 => original i)) ∧
      (∀ x : E → R,
        localKernelCondition attached x ↔ localKernelCondition original x) ∧
      (∀ context' : RootedContext,
        aggregateJet (R := R) context = aggregateJet (R := R) context' →
          attachedFamilyFeatureMatrix context events distinguished =
            attachedFamilyFeatureMatrix (R := R) (E := E) (P := P)
            context' events distinguished)

end
end MathlibPlus.Open.ResearchFormalization.R0913
