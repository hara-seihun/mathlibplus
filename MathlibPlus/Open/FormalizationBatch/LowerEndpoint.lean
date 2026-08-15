import Mathlib

namespace MathlibPlus.Open.FormalizationBatch

noncomputable def batchNeighbors {V : Type*} [Fintype V]
    (G : SimpleGraph V) (v : V) : Finset V := by
  classical
  exact Finset.univ.filter (fun w => G.Adj v w)

noncomputable def batchNonNeighbors {V : Type*} [Fintype V]
    (G : SimpleGraph V) (v : V) : Finset V := by
  classical
  exact Finset.univ.filter (fun w => w ≠ v ∧ ¬G.Adj v w)

noncomputable def batchEdgeCountOn {V : Type*} [Fintype V]
    (G : SimpleGraph V) (U : Finset V) : ℕ := by
  classical
  exact (U.sum (fun x => (U.filter (fun y => G.Adj x y)).card)) / 2

noncomputable def batchComplementEdgeCountOn {V : Type*} [Fintype V]
    (G : SimpleGraph V) (U : Finset V) : ℕ := by
  classical
  exact
    (U.sum (fun x =>
      (U.filter (fun y => x ≠ y ∧ ¬G.Adj x y)).card)) / 2

noncomputable def batchLocalP {V : Type*} [Fintype V]
    (G : SimpleGraph V) (v : V) : ℕ :=
  batchEdgeCountOn G (batchNeighbors G v)

noncomputable def batchLocalH {V : Type*} [Fintype V]
    (G : SimpleGraph V) (v : V) : ℕ :=
  batchComplementEdgeCountOn G (batchNonNeighbors G v)

noncomputable def batchGlobalE {V : Type*} [Fintype V]
    (G : SimpleGraph V) : ℕ :=
  batchEdgeCountOn G Finset.univ

def batchPairs43 (p h : ℕ) : Prop :=
  (p = 81 ∧ h = 132) ∨
    (p = 82 ∧ h = 131) ∨
    (p = 83 ∧ h = 130) ∨
    (p = 84 ∧ h = 129) ∨
    (p = 85 ∧ h = 128)

def batchPairs44 (p h : ℕ) : Prop :=
  (p = 87 ∧ h = 132) ∨
    (p = 88 ∧ h = 131) ∨
    (p = 89 ∧ h = 130) ∨
    (p = 90 ∧ h = 129) ∨
    (p = 91 ∧ h = 128) ∨
    (p = 92 ∧ h = 127)

def batchPairs45 (p h : ℕ) : Prop :=
  (p = 94 ∧ h = 132) ∨
    (p = 95 ∧ h = 131) ∨
    (p = 96 ∧ h = 130) ∨
    (p = 97 ∧ h = 129) ∨
    (p = 98 ∧ h = 128) ∨
    (p = 99 ∧ h = 127) ∨
    (p = 100 ∧ h = 126)

def lowerEndpointLocalNeighbourhoodIdentity
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (n d : ℕ) : Prop :=
  n = Fintype.card V ∧
    (∀ v : V, (batchNeighbors G v).card = d) ∧
    n - 25 = d ∧
    batchGlobalE G = n * d / 2 ∧
    (∀ v : V,
      (batchNonNeighbors G v).card = 24 ∧
        (batchLocalP G v : ℤ) + (batchLocalH G v : ℤ) =
          (d : ℤ) ^ 2 - (batchGlobalE G : ℤ) + (Nat.choose 24 2 : ℤ)) ∧
    (∀ v : V,
      ((n = 43 ∧ d = 18) → batchPairs43 (batchLocalP G v) (batchLocalH G v)) ∧
      ((n = 44 ∧ d = 19) → batchPairs44 (batchLocalP G v) (batchLocalH G v)) ∧
      ((n = 45 ∧ d = 20) → batchPairs45 (batchLocalP G v) (batchLocalH G v)))

end MathlibPlus.Open.FormalizationBatch
