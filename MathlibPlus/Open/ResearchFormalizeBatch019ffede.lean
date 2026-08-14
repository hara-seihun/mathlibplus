import Mathlib

namespace MathlibPlus.Open.ResearchFormalizeBatch

open scoped BigOperators

abbrev R := MvPolynomial (Fin 2) ℚ

inductive RootedTree where
  | node (branches : List RootedTree)
  deriving Repr

namespace RootedTree

def size : RootedTree → Nat
  | .node branches => 1 + (branches.map size).sum

def branchSize (branches : List RootedTree) : Nat :=
  (branches.map size).sum

end RootedTree

inductive MessageTask where
  | pTree (tree : RootedTree)
  | rhoTree (tree : RootedTree)
  | nuTree (tree : RootedTree)
  | pList (branches : List RootedTree)
  | nuList (branches : List RootedTree)

namespace MessageTask

def measure : MessageTask → Nat
  | .pTree t => 2 * RootedTree.size t
  | .rhoTree t => 2 * RootedTree.size t
  | .nuTree t => 2 * RootedTree.size t
  | .pList ts => 2 * RootedTree.branchSize ts + 1
  | .nuList ts => 2 * RootedTree.branchSize ts + 1

end MessageTask

noncomputable def qvar : R := MvPolynomial.X 0
noncomputable def avar : R := MvPolynomial.X 1

noncomputable def messageEval : MessageTask → R
  | .pTree (.node branches) =>
      avar * messageEval (.pList branches) +
        (qvar - avar) * messageEval (.nuList branches)
  | .rhoTree (.node branches) => messageEval (.pList branches)
  | .nuTree (.node branches) =>
      (avar - 1) * messageEval (.pList branches) +
        (qvar - avar) * messageEval (.nuList branches)
  | .pList [] => 1
  | .pList (tree :: trees) =>
      messageEval (.pTree tree) * messageEval (.pList trees)
  | .nuList [] => 1
  | .nuList (tree :: trees) =>
      messageEval (.nuTree tree) * messageEval (.nuList trees)
termination_by task => task.measure
decreasing_by
  all_goals simp [MessageTask.measure, RootedTree.size, RootedTree.branchSize,
    Nat.mul_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
  all_goals
    try
      cases tree <;> simp [RootedTree.size]
  all_goals omega

noncomputable def pMessage (T : RootedTree) : R := messageEval (.pTree T)
noncomputable def rhoMessage (T : RootedTree) : R := messageEval (.rhoTree T)
noncomputable def nuMessage (T : RootedTree) : R := messageEval (.nuTree T)

noncomputable def shiftedNu (T : RootedTree) : R :=
  MvPolynomial.eval₂ (algebraMap ℚ R)
    (fun i =>
      if i = (0 : Fin 2) then 1 + MvPolynomial.X 0
      else 1 + MvPolynomial.X 1)
    (nuMessage T)

noncomputable def evalAt (q a : ℚ) (f : R) : ℚ :=
  MvPolynomial.eval₂ (RingHom.id ℚ)
    (fun i => if i = (0 : Fin 2) then q else a) f

noncomputable def exponent (i j : ℕ) : Fin 2 →₀ ℕ :=
  Finsupp.single (0 : Fin 2) i + Finsupp.single (1 : Fin 2) j

def monicOuter (f : R) (n : ℕ) : Prop :=
  MvPolynomial.coeff (exponent n 0) f = 1 ∧
    (∀ m ∈ f.support, m 0 ≤ n) ∧
    (∀ m ∈ f.support, m 0 = n → m 1 = 0)

def lowerXCoefficientsDivisibleByY (f : R) (n : ℕ) : Prop :=
  ∀ m ∈ f.support, m 0 < n → 0 < m 1

def constantXCoefficientHasYOrderOne (f : R) : Prop :=
  (∀ m ∈ f.support, m 0 = 0 → 0 < m 1) ∧
    MvPolynomial.coeff (exponent 0 1) f ≠ 0

def isEisensteinAtY (f : R) (n : ℕ) : Prop :=
  monicOuter f n ∧
    lowerXCoefficientsDivisibleByY f n ∧
    constantXCoefficientHasYOrderOne f

def specializesToXPower (T : RootedTree) : Prop :=
  ∀ x : ℚ,
    evalAt x 0 (shiftedNu T) = x ^ RootedTree.size T

def claim24254 : Prop :=
  ∀ T : RootedTree,
    MvPolynomial.totalDegree (pMessage T) ≤ RootedTree.size T ∧
    MvPolynomial.totalDegree (rhoMessage T) ≤ RootedTree.size T - 1 ∧
    MvPolynomial.totalDegree (nuMessage T) ≤ RootedTree.size T ∧
    MvPolynomial.totalDegree (shiftedNu T) ≤ RootedTree.size T

def claim24255 : Prop :=
  ∀ T : RootedTree,
    specializesToXPower T ∧
    monicOuter (shiftedNu T) (RootedTree.size T) ∧
    lowerXCoefficientsDivisibleByY (shiftedNu T) (RootedTree.size T)

def claim24256 : Prop :=
  ∀ branches : List RootedTree, branches ≠ [] →
    let T := RootedTree.node branches
    constantXCoefficientHasYOrderOne (shiftedNu T) ∧
      (∀ y : ℚ,
        evalAt 0 y (shiftedNu T) =
          y * (evalAt 1 (1 + y) (rhoMessage T) -
            evalAt 1 (1 + y) (messageEval (.nuList branches)))) ∧
      (evalAt 1 1 (rhoMessage T) -
        evalAt 1 1 (messageEval (.nuList branches)) = 1)

def claim24257 : Prop :=
  (∀ T : RootedTree, RootedTree.size T = 1 → shiftedNu T = MvPolynomial.X 0) ∧
    (∀ T : RootedTree, 1 < RootedTree.size T →
      isEisensteinAtY (shiftedNu T) (RootedTree.size T)) ∧
    (∀ T : RootedTree, Irreducible (shiftedNu T)) ∧
    (∀ T : RootedTree, Irreducible (nuMessage T))

def claim24259 : Prop :=
  ∀ A B C D : RootedTree,
    pMessage A * pMessage C = pMessage B * pMessage D →
    nuMessage A * nuMessage C = nuMessage B * nuMessage D →
    (nuMessage A = nuMessage B ∧ nuMessage C = nuMessage D) ∨
      (nuMessage A = nuMessage D ∧ nuMessage C = nuMessage B)

abbrev BinaryAssignment (V : Type) (r : Nat) := V → Fin (r + 1) → Bool
abbrev BinaryCoverAssignment (V : Type) (r : Nat) := V → V → Fin (r + 1) → Bool

def bit (b : Bool) : Nat := if b then 1 else 0

def possibleStart (r k a : Nat) : Prop := a ≤ k ∧ k ≤ r - a

def gradedRank {V : Type} [PartialOrder V] (r : Nat)
    (rank : V → Fin (r + 1)) : Prop :=
  ∀ ⦃v w : V⦄, CovBy v w → (rank w).val = (rank v).val + 1

def edgePossible {V : Type} [PartialOrder V] (r : Nat)
    (rank : V → Fin (r + 1)) (v w : V) (a : Fin (r + 1)) : Prop :=
  CovBy v w ∧ a.val ≤ (rank v).val ∧ (rank w).val ≤ r - a.val

noncomputable def startRanks {V : Type} [Fintype V] (r : Nat)
    (rank : V → Fin (r + 1)) (v : V) : Finset (Fin (r + 1)) := by
  classical
  exact Finset.univ.filter (fun a => possibleStart r (rank v).val a.val)

noncomputable def incomingCount {V : Type} [Fintype V] [PartialOrder V]
    (r : Nat) (rank : V → Fin (r + 1)) (x : BinaryCoverAssignment V r)
    (v : V) (a : Fin (r + 1)) : Nat := by
  classical
  exact ∑ u : V, if CovBy u v then bit (x u v a) else 0

noncomputable def outgoingCount {V : Type} [Fintype V] [PartialOrder V]
    (r : Nat) (rank : V → Fin (r + 1)) (x : BinaryCoverAssignment V r)
    (v : V) (a : Fin (r + 1)) : Nat := by
  classical
  exact ∑ w : V, if CovBy v w then bit (x v w a) else 0

def binaryCoverFlowFeasible {V : Type} [Fintype V] [PartialOrder V]
    (r : Nat) (rank : V → Fin (r + 1))
    (z : BinaryAssignment V r) (x : BinaryCoverAssignment V r) : Prop :=
  gradedRank r rank ∧
    (∀ v : V, Finset.sum (startRanks r rank v) (fun a => bit (z v a)) = 1) ∧
    (∀ v : V, ∀ a : Fin (r + 1),
      ¬ possibleStart r (rank v).val a.val → z v a = false) ∧
    (∀ v w : V, ∀ a : Fin (r + 1),
      ¬ edgePossible r rank v w a → x v w a = false) ∧
    (∀ v : V, ∀ a : Fin (r + 1),
      a.val < (rank v).val → incomingCount r rank x v a = bit (z v a)) ∧
    (∀ v : V, ∀ a : Fin (r + 1),
      (rank v).val < r - a.val → outgoingCount r rank x v a = bit (z v a))

def allSelected {V : Type} (z : BinaryAssignment V r) (a : Fin (r + 1)) :
    List V → Prop
  | [] => True
  | v :: vs => z v a = true ∧ allSelected z a vs

def adjacentSelected {V : Type} (x : BinaryCoverAssignment V r)
    (a : Fin (r + 1)) : List V → Prop
  | [] => True
  | [_] => True
  | v :: w :: vs => x v w a = true ∧ adjacentSelected x a (w :: vs)

def firstVertex {V : Type} : List V → Option V
  | [] => none
  | v :: _ => some v

def lastVertex {V : Type} : List V → Option V
  | [] => none
  | [v] => some v
  | _ :: vs => lastVertex vs

def selectedPath {V : Type} [PartialOrder V]
    (r : Nat) (rank : V → Fin (r + 1))
    (z : BinaryAssignment V r) (x : BinaryCoverAssignment V r)
    (a : Fin (r + 1)) (path : List V) : Prop :=
  path ≠ [] ∧
    allSelected z a path ∧
    adjacentSelected x a path ∧
    path.Nodup ∧
    (∃ first last : V,
      firstVertex path = some first ∧
      lastVertex path = some last ∧
      (rank first).val = a.val ∧
      (rank last).val = r - a.val)

def adjacentPair {V : Type} (u v : V) : List V → Prop
  | [] => False
  | [_] => False
  | first :: second :: rest =>
      (first = u ∧ second = v) ∨ adjacentPair u v (second :: rest)

def pathDecomposition {V : Type} [PartialOrder V]
    (r : Nat) (rank : V → Fin (r + 1))
    (z : BinaryAssignment V r) (x : BinaryCoverAssignment V r)
    (a : Fin (r + 1)) (paths : List (List V)) : Prop :=
  paths.Nodup ∧
    (∀ path ∈ paths, selectedPath r rank z x a path) ∧
    (∀ v : V,
      z v a = true ↔ ∃! path, path ∈ paths ∧ v ∈ path) ∧
    (∀ u v : V,
      x u v a = true ↔ ∃ path, path ∈ paths ∧ adjacentPair u v path)

def claim24268 : Prop :=
  ∀ {V : Type} [Fintype V] [PartialOrder V]
    (r : Nat) (rank : V → Fin (r + 1))
    (z : BinaryAssignment V r) (x : BinaryCoverAssignment V r),
    binaryCoverFlowFeasible r rank z x →
      ∀ a : Fin (r + 1),
        ∃ paths : List (List V), pathDecomposition r rank z x a paths

def rankSet {V : Type} (rank : V → Fin (r + 1)) (k : Nat) : Type :=
  {v : V // (rank v).val = k}

def samePath {V : Type} (paths : List (List V)) (v w : V) : Prop :=
  ∃ path, path ∈ paths ∧ v ∈ path ∧ w ∈ path

def symmetricChainDecomposition {V : Type} [PartialOrder V]
    (r : Nat) (rank : V → Fin (r + 1))
    (z : BinaryAssignment V r) (x : BinaryCoverAssignment V r)
    (paths : Fin (r + 1) → List (List V)) : Prop :=
  (∀ a : Fin (r + 1), pathDecomposition r rank z x a (paths a)) ∧
    (∀ v : V, ∃! a : Fin (r + 1), z v a = true)

def claim24273 : Prop :=
  ∀ {V : Type} [Fintype V] [PartialOrder V]
    (r : Nat) (rank : V → Fin (r + 1))
    (z : BinaryAssignment V r) (x : BinaryCoverAssignment V r)
    (paths : Fin (r + 1) → List (List V)),
    symmetricChainDecomposition r rank z x paths →
      ∀ k : Nat, k ≤ r - k →
        ∃ raising : rankSet rank k ≃ rankSet rank (r - k),
          ∀ v : rankSet rank k,
            ∃ a : Fin (r + 1), samePath (paths a) v.1 (raising v).1

abbrev LiftedAssignment (V : Type) (r K : Nat) :=
  V → Fin (r + 1) → Fin (K + 1) → Bool
abbrev LiftedCoverAssignment (V : Type) (r K : Nat) :=
  V → V → Fin (r + 1) → Fin (K + 1) → Bool

noncomputable def counterStep {V State : Type} [DecidableEq State]
    (σ : V → State) (u v : V) (K : Nat) (q : Fin (K + 1)) : Option (Fin (K + 1)) := by
  classical
  by_cases h : σ u = σ v
  · exact some q
  · by_cases hq : q.val < K
    · exact some ⟨q.val + 1, by omega⟩
    · exact none

def liftedEdgePossible {V State : Type} [PartialOrder V] [DecidableEq State]
    (r K : Nat) (rank : V → Fin (r + 1)) (σ : V → State)
    (u v : V) (a : Fin (r + 1)) (q : Fin (K + 1)) : Prop :=
  edgePossible r rank u v a ∧ counterStep σ u v K q ≠ none

noncomputable def liftedIncomingCount {V State : Type} [Fintype V] [PartialOrder V]
    [DecidableEq State] (r K : Nat) (rank : V → Fin (r + 1)) (σ : V → State)
    (x : LiftedCoverAssignment V r K) (v : V) (a : Fin (r + 1))
    (q : Fin (K + 1)) : Nat := by
  classical
  exact ∑ u : V, ∑ q0 : Fin (K + 1),
    if CovBy u v ∧ counterStep σ u v K q0 = some q then
      bit (x u v a q0)
    else 0

noncomputable def liftedOutgoingCount {V State : Type} [Fintype V] [PartialOrder V]
    [DecidableEq State] (r K : Nat) (rank : V → Fin (r + 1)) (σ : V → State)
    (x : LiftedCoverAssignment V r K) (v : V) (a : Fin (r + 1))
    (q : Fin (K + 1)) : Nat := by
  classical
  exact ∑ w : V, if CovBy v w then bit (x v w a q) else 0

def liftedCounterFlowFeasible {V State : Type} [Fintype V] [PartialOrder V]
    [DecidableEq State] (r K : Nat) (rank : V → Fin (r + 1))
    (σ : V → State) (z : LiftedAssignment V r K)
    (x : LiftedCoverAssignment V r K) : Prop :=
  gradedRank r rank ∧
    (∀ v : V,
      Finset.sum Finset.univ (fun a =>
        Finset.sum Finset.univ (fun q => bit (z v a q))) = 1) ∧
    (∀ v : V, ∀ a : Fin (r + 1), ∀ q : Fin (K + 1),
      ¬ possibleStart r (rank v).val a.val → z v a q = false) ∧
    (∀ v : V, ∀ a : Fin (r + 1), ∀ q : Fin (K + 1),
      (rank v).val = a.val ∧ q.val ≠ 0 → z v a q = false) ∧
    (∀ u v : V, ∀ a : Fin (r + 1), ∀ q : Fin (K + 1),
      ¬ liftedEdgePossible r K rank σ u v a q → x u v a q = false) ∧
    (∀ v : V, ∀ a : Fin (r + 1), ∀ q : Fin (K + 1),
      a.val < (rank v).val →
        liftedIncomingCount r K rank σ x v a q = bit (z v a q)) ∧
    (∀ v : V, ∀ a : Fin (r + 1), ∀ q : Fin (K + 1),
      (rank v).val < r - a.val →
        liftedOutgoingCount r K rank σ x v a q = bit (z v a q))

noncomputable def projectAssignment {V : Type} (r K : Nat)
    (z : LiftedAssignment V r K) : BinaryAssignment V r := by
  classical
  exact fun v a => if ∃ q : Fin (K + 1), z v a q = true then true else false

noncomputable def projectCoverAssignment {V : Type} (r K : Nat)
    (x : LiftedCoverAssignment V r K) : BinaryCoverAssignment V r := by
  classical
  exact fun u v a => if ∃ q : Fin (K + 1), x u v a q = true then true else false

def claim24269 : Prop :=
  ∀ {V State : Type} [Fintype V] [PartialOrder V] [DecidableEq State]
    (r K : Nat) (rank : V → Fin (r + 1)) (σ : V → State)
    (z : LiftedAssignment V r K) (x : LiftedCoverAssignment V r K),
    liftedCounterFlowFeasible r K rank σ z x →
      binaryCoverFlowFeasible r rank
        (projectAssignment r K z) (projectCoverAssignment r K x)

def switchCount {V State : Type} [DecidableEq State]
    (σ : V → State) : List V → Nat
  | [] => 0
  | [_] => 0
  | u :: v :: rest =>
      (if σ u = σ v then 0 else 1) + switchCount σ (v :: rest)

def boundedSwitchSCD {V State : Type} [Fintype V] [PartialOrder V]
    [DecidableEq State] (r K : Nat) (rank : V → Fin (r + 1))
    (σ : V → State) : Prop :=
  ∃ (z : BinaryAssignment V r) (x : BinaryCoverAssignment V r)
    (paths : Fin (r + 1) → List (List V)),
    binaryCoverFlowFeasible r rank z x ∧
      symmetricChainDecomposition r rank z x paths ∧
      ∀ a : Fin (r + 1), ∀ path ∈ paths a,
        switchCount σ path ≤ K

def claim24270 : Prop :=
  ∀ {V State : Type} [Fintype V] [PartialOrder V] [DecidableEq State]
    (r K : Nat) (rank : V → Fin (r + 1)) (σ : V → State),
    (∃ z : LiftedAssignment V r K, ∃ x : LiftedCoverAssignment V r K,
      liftedCounterFlowFeasible r K rank σ z x) ↔
      boundedSwitchSCD r K rank σ

def claim24272 : Prop :=
  ∀ {V State : Type} [Fintype V] [PartialOrder V] [DecidableEq State]
    (r K : Nat) (rank : V → Fin (r + 1)) (σ : V → State),
    (¬ ∃ z : LiftedAssignment V r K, ∃ x : LiftedCoverAssignment V r K,
      liftedCounterFlowFeasible r K rank σ z x) →
      ¬ boundedSwitchSCD r K rank σ

end MathlibPlus.Open.ResearchFormalizeBatch
