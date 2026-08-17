import Mathlib

noncomputable section

namespace MathlibPlus.Open.ResearchFormalization.Batch61149

open scoped BigOperators
attribute [local instance] Classical.decEq Classical.propDecidable

abbrev FrameVector (p r : ℕ) := Fin r → ZMod p
abbrev FrameMatrix (p r k : ℕ) := Matrix (Fin r) (Fin k) (ZMod p)

def frameColumn {p r k : ℕ} (A : FrameMatrix p r k) (j : Fin k) : FrameVector p r :=
  fun i => A i j

def frameHammingWeight {p r : ℕ} (v : FrameVector p r) : ℕ :=
  Fintype.card {i : Fin r // v i ≠ 0}

def frameHypotheses {p r k : ℕ} (A : FrameMatrix p r k) : Prop :=
  Function.Injective A.mulVec ∧
    (∀ v : FrameVector p r, v ∈ Set.range A.mulVec → v ≠ 0 →
      4 ≤ frameHammingWeight v) ∧
    (∀ i : Fin r, ∃ j : Fin k, A i j ≠ 0)

def frameBasisVector {p r : ℕ} (i : Fin r) : FrameVector p r :=
  fun l => if l = i then 1 else 0

def signedFrameBasisDirections {p r : ℕ} : Set (FrameVector p r) :=
  {v | ∃ i : Fin r, v = frameBasisVector i ∨ v = -frameBasisVector i}

def signedFrameColumnDirections {p r k : ℕ} (A : FrameMatrix p r k) :
    Set (FrameVector p r) :=
  {v | ∃ j : Fin k, v = frameColumn A j ∨ v = -frameColumn A j}

def frameConnectionSet {p r k : ℕ} (A : FrameMatrix p r k) :
    Set (FrameVector p r) :=
  signedFrameBasisDirections ∪ signedFrameColumnDirections A

def frameIdentityFree {p r : ℕ} (S : Set (FrameVector p r)) : Prop :=
  0 ∉ S

def frameInverseClosed {p r : ℕ} (S : Set (FrameVector p r)) : Prop :=
  ∀ x : FrameVector p r, x ∈ S ↔ -x ∈ S

def frameShortOppositePairRelation {p r : ℕ}
    (S : Set (FrameVector p r)) : Prop :=
  ∀ m : Multiset (FrameVector p r),
    m.card ≤ 4 →
      (∀ x, x ∈ m → x ∈ S) →
        m.sum = 0 →
          ∃ u : Multiset (FrameVector p r),
            m = u + u.map (fun x => -x)

def frameAdditiveCayleyGraph {p r : ℕ}
    (S : Set (FrameVector p r)) : SimpleGraph (FrameVector p r) :=
  SimpleGraph.fromRel (fun x y => y - x ∈ S)

def frameSpanning {p r : ℕ} (S : Set (FrameVector p r)) : Prop :=
  Submodule.span (ZMod p) S = ⊤

def frameAffine {p r : ℕ}
    (S T : Set (FrameVector p r))
    (e : SimpleGraph.Iso (frameAdditiveCayleyGraph S)
      (frameAdditiveCayleyGraph T)) : Prop :=
  ∃ L : FrameVector p r ≃ₗ[ZMod p] FrameVector p r,
    ∃ b : FrameVector p r, ∀ x, e x = L x + b

-- The parameters `S` and `T` are explicit through the graph arguments above.
def frameOrdinaryUndirectedCI {p r : ℕ}
    (S : Set (FrameVector p r)) : Prop :=
  frameIdentityFree S ∧
    frameInverseClosed S ∧
      ∀ T : Set (FrameVector p r),
        frameIdentityFree T →
          frameInverseClosed T →
            ∀ e : SimpleGraph.Iso (frameAdditiveCayleyGraph S)
              (frameAdditiveCayleyGraph T),
              ∃ L : FrameVector p r ≃ₗ[ZMod p] FrameVector p r,
                L '' S = T

def frameConclusion {p r k : ℕ} (A : FrameMatrix p r k) : Prop :=
  let S := frameConnectionSet A
  frameIdentityFree S ∧
    frameInverseClosed S ∧
    frameSpanning S ∧
    Set.ncard S = 2 * (r + k) ∧
    frameShortOppositePairRelation S ∧
    (∀ T : Set (FrameVector p r),
      frameIdentityFree T →
        frameInverseClosed T →
          ∀ e : SimpleGraph.Iso (frameAdditiveCayleyGraph S)
            (frameAdditiveCayleyGraph T),
            frameAffine S T e ∧
              ∃ L : FrameVector p r ≃ₗ[ZMod p] FrameVector p r,
                L '' S = T) ∧
    frameOrdinaryUndirectedCI S

abbrev HomogeneousRepresentative (p : ℕ) := Fin 2 → ZMod p

def projectivelyEquivalent {p : ℕ}
    (x y : HomogeneousRepresentative p) : Prop :=
  ∃ c : ZMod p, c ≠ 0 ∧ x = c • y

def projectiveRepresentativeFamily {p n : ℕ}
    (q : Fin n → HomogeneousRepresentative p) : Prop :=
  (∀ i : Fin n, q i ≠ 0) ∧
    (∀ i j : Fin n, i ≠ j → ¬ projectivelyEquivalent (q i) (q j))

def veroneseRow (p k : ℕ) (x : HomogeneousRepresentative p)
    (j : Fin k) : ZMod p :=
  (x (1 : Fin 2)) ^ (k - 1 - j.1) * (x (0 : Fin 2)) ^ j.1

def projectiveFrameMatrix (p r k : ℕ)
    (q : Fin (min r (p + 1)) → HomogeneousRepresentative p) :
    FrameMatrix p r k :=
  fun i j =>
    if h : i.1 < min r (p + 1) then
      veroneseRow p k (q ⟨i.1, h⟩) j
    else
      veroneseRow p k ![0, 1] j

def projectiveFrameConstruction : Prop :=
  ∀ (p r k : ℕ),
    Nat.Prime p →
      5 ≤ p →
        1 ≤ r →
          1 ≤ k →
            k ≤ min r (p + 1) - 3 →
              ∃ q : Fin (min r (p + 1)) → HomogeneousRepresentative p,
                projectiveRepresentativeFamily q ∧
                  frameHypotheses (projectiveFrameMatrix p r k q) ∧
                    frameConclusion (projectiveFrameMatrix p r k q)

def maintainedProjectiveFrameValencies : Prop :=
  ∀ (p r : ℕ),
    Nat.Prime p →
      5 ≤ p →
        6 ≤ r →
          r ≤ 2 * p + 2 →
            (∀ k : ℕ,
              1 ≤ k →
                k ≤ min r (p + 1) - 3 →
                  ∃ q : Fin (min r (p + 1)) → HomogeneousRepresentative p,
                    projectiveRepresentativeFamily q ∧
                      frameConclusion (projectiveFrameMatrix p r k q)) ∧
            (∃ q : Fin (min r (p + 1)) → HomogeneousRepresentative p,
              projectiveRepresentativeFamily q ∧
                frameConclusion (projectiveFrameMatrix p r 3 q) ∧
                  Set.ncard (frameConnectionSet
                    (projectiveFrameMatrix p r 3 q)) = 2 * r + 6)

def claim61149 : Prop :=
  (∀ (p r k : ℕ),
      Nat.Prime p →
        5 ≤ p →
          1 ≤ r →
            1 ≤ k →
              ∀ A : FrameMatrix p r k,
                frameHypotheses A →
                  frameConclusion A) ∧
  projectiveFrameConstruction ∧
  maintainedProjectiveFrameValencies


end MathlibPlus.Open.ResearchFormalization.Batch61149
