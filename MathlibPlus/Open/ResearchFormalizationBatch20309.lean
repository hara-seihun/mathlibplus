import Mathlib
import MathlibPlus.Open.Research.FormalizationBatchUPolynomial

open scoped BigOperators
open Classical

namespace MathlibPlus.Open.ResearchFormalizationBatch20309

noncomputable section

abbrev ForestPolynomial := MvPolynomial ℕ ℤ
abbrev RootedPolynomial := Polynomial ForestPolynomial

def forestOnSubset {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (S : Finset V) : ForestPolynomial :=
  MathlibPlus.Open.ResearchFormalizationBatch.forestUPolynomial
    (G.induce (S : Set V))

def restrictedReachable {V : Type}
    (G : SimpleGraph V) (S : Finset V) (u v : V) : Prop :=
  Relation.ReflTransGen
    (fun a b => G.Adj a b ∧ a ∈ S ∧ b ∈ S) u v

def rootedConnectedSubset {V : Type} [DecidableEq V]
    (G : SimpleGraph V) (S Q : Finset V) (r : V) : Prop :=
  Q.Nonempty ∧ r ∈ Q ∧
    ∀ v ∈ Q, restrictedReachable G Q r v

def rootedROnSubset {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (S : Finset V) (r : V) : RootedPolynomial :=
  ∑ Q ∈ S.powerset.filter (rootedConnectedSubset G S · r),
    Polynomial.C (forestOnSubset G (S \ Q)) * Polynomial.X ^ Q.card

def rootedR {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (r : V) : RootedPolynomial :=
  rootedROnSubset G (Finset.univ : Finset V) r

def rootedFactor {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (r : V) : RootedPolynomial :=
  rootedR G r + Polynomial.C (forestOnSubset G (Finset.univ : Finset V))

def positiveZPart (F : RootedPolynomial) : RootedPolynomial :=
  F - Polynomial.C (F.coeff 0)

def rootedRQuotientOnSubset {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (S : Finset V) (r : V) : RootedPolynomial :=
  ∑ Q ∈ S.powerset.filter (rootedConnectedSubset G S · r),
    Polynomial.C (forestOnSubset G (S \ Q)) * Polynomial.X ^ (Q.card - 1)

def rootedRQuotient {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (r : V) : RootedPolynomial :=
  rootedRQuotientOnSubset G (Finset.univ : Finset V) r

structure BranchPiece (V : Type) where
  vertices : Finset V
  root : V
  deriving DecidableEq, Fintype

def componentSubset {V : Type} [DecidableEq V]
    (G : SimpleGraph V) (S : Finset V) (r : V) : Finset V :=
  S.filter (restrictedReachable G S r)

def isChildBranch {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (r : V) (B : BranchPiece V) : Prop :=
  B.root ∈ B.vertices ∧ B.root ≠ r ∧ G.Adj r B.root ∧
    B.vertices = componentSubset G (Finset.univ.erase r) B.root

def childBranches {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (r : V) : Finset (BranchPiece V) :=
  Finset.univ.filter (isChildBranch G r)

def rootedFactorOnBranch {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (B : BranchPiece V) : RootedPolynomial :=
  rootedROnSubset G B.vertices B.root +
    Polynomial.C (forestOnSubset G B.vertices)

def childFactorProduct {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (r : V) : RootedPolynomial :=
  ∏ B ∈ childBranches G r, rootedFactorOnBranch G B

def rootedIso {V W : Type}
    (G : SimpleGraph V) (r : V) (H : SimpleGraph W) (s : W) : Prop :=
  ∃ e : V ≃ W, e r = s ∧
    ∀ u v, G.Adj u v ↔ H.Adj (e u) (e v)

/-- Claim 20309: a genuine rooted factor exposes its positive-`z` rooted
part; the quotient by `z` is the product over the actual child branches, and
that factorization together with induction determines the rooted tree. -/
def claim_20309 : Prop :=
  ∀ {V W : Type}
    [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) (r : V) (H : SimpleGraph W) (s : W),
    G.IsTree → H.IsTree →
      rootedFactor G r = rootedFactor H s →
        positiveZPart (rootedFactor G r) = positiveZPart (rootedFactor H s) ∧
        rootedR G r = rootedR H s ∧
        rootedRQuotient G r = childFactorProduct G r ∧
        rootedRQuotient H s = childFactorProduct H s ∧
        rootedIso G r H s

end
end MathlibPlus.Open.ResearchFormalizationBatch20309
