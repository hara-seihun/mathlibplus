import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.OracleArea.Claim60095

abbrev RademacherSign := Bool

def signValue (s : RademacherSign) : ℝ :=
  if s then 1 else -1

inductive CoordinateTree (ι : Type) where
  | leaf : ι → CoordinateTree ι
  | branch : ι → CoordinateTree ι → CoordinateTree ι → CoordinateTree ι

namespace CoordinateTree

def eval : CoordinateTree ι → (ι → RademacherSign) → RademacherSign
  | .leaf i, ω => ω i
  | .branch i positive negative, ω =>
      if ω i then eval positive ω else eval negative ω

def depth : CoordinateTree ι → ℕ
  | .leaf _ => 0
  | .branch _ positive negative => 1 + max positive.depth negative.depth

end CoordinateTree

abbrev CoordinateN (n : ℕ) := Fin (2 * n + 1)
abbrev OracleN (n : ℕ) := CoordinateN n → RademacherSign
abbrev HistoryN (n : ℕ) := CoordinateN n → Option RademacherSign

private def xCoordinate (n : ℕ) : CoordinateN n :=
  ⟨0, by omega⟩

private def rCoordinate (n : ℕ) (j : Fin n) : CoordinateN n :=
  ⟨1 + j.1, by omega⟩

private def yCoordinate (n : ℕ) (j : Fin n) : CoordinateN n :=
  ⟨1 + n + j.1, by omega⟩

private def treeN (n : ℕ) (j : Fin n) : CoordinateTree (CoordinateN n) :=
  .branch (rCoordinate n j)
    (.leaf (xCoordinate n))
    (.leaf (yCoordinate n j))

private noncomputable def targetN (n : ℕ) (ω : OracleN n) : ℝ :=
  (∑ j : Fin n, signValue ((treeN n j).eval ω)) / (n : ℝ)

structure CoordinatePolicyN (n : ℕ) where
  next : HistoryN n → Option (CoordinateN n)

private def LegalPolicyN {n : ℕ} (p : CoordinatePolicyN n) : Prop :=
  ∀ (h : HistoryN n) (c : CoordinateN n), p.next h = some c → h c = none

private def emptyHistoryN (n : ℕ) : HistoryN n := fun _ => none

private def revealN {n : ℕ} (h : HistoryN n) (c : CoordinateN n)
    (ω : OracleN n) : HistoryN n :=
  Function.update h c (some (ω c))

private def pendingIndex (n : ℕ) (h : HistoryN n) (j : Fin n) : Prop :=
  h (rCoordinate n j) = none ∨
    (h (rCoordinate n j) = some false ∧ h (yCoordinate n j) = none)

private noncomputable def firstPending (n : ℕ) (h : HistoryN n) : Option (Fin n) := by
  classical
  let S := Finset.univ.filter (fun j : Fin n => pendingIndex n h j)
  by_cases hS : S.Nonempty
  · exact some (S.min' hS)
  · exact none

private noncomputable def legalPolicyN (n : ℕ) : CoordinatePolicyN n :=
  { next := fun h =>
      if h (xCoordinate n) = none then
        some (xCoordinate n)
      else
        match firstPending n h with
        | none => none
        | some j =>
            if h (rCoordinate n j) = none then
              some (rCoordinate n j)
            else
              some (yCoordinate n j) }

private def transcriptN (p : CoordinatePolicyN n) (ω : OracleN n) : ℕ → HistoryN n
  | 0 => emptyHistoryN n
  | m + 1 =>
      let h := transcriptN p ω m
      match p.next h with
      | none => h
      | some c => revealN h c ω

private def consistentN (h : HistoryN n) (ω : OracleN n) : Prop :=
  ∀ (c : CoordinateN n) (s : RademacherSign), h c = some s → ω c = s

private noncomputable def fiberN (h : HistoryN n) : Finset (OracleN n) := by
  classical
  exact Finset.univ.filter (fun ω => consistentN h ω)

private noncomputable def posteriorVarianceN
    (f : OracleN n → ℝ) (h : HistoryN n) : ℝ :=
  let S := fiberN h
  if S.Nonempty then
    let q : ℝ := S.card
    (∑ ω ∈ S, (f ω) ^ 2) / q - ((∑ ω ∈ S, f ω) / q) ^ 2
  else
    0

private noncomputable def expectedPosteriorVarianceN
    (f : OracleN n → ℝ) (h : OracleN n → HistoryN n) : ℝ :=
  (∑ ω : OracleN n, posteriorVarianceN f (h ω)) /
    (Fintype.card (OracleN n) : ℝ)

private noncomputable def rootInclusiveAreaN
    (n : ℕ) (p : CoordinatePolicyN n) (f : OracleN n → ℝ) : ℝ :=
  ∑ m : Fin (2 * n + 2),
    expectedPosteriorVarianceN f (fun ω => transcriptN p ω m.1)

private def residualRoot5 (j : Fin 5) (h : HistoryN 5) : Option (CoordinateN 5) :=
  if h (rCoordinate 5 j) = none then
    some (rCoordinate 5 j)
  else if h (rCoordinate 5 j) = some true then
    if h (xCoordinate 5) = none then some (xCoordinate 5) else none
  else
    if h (yCoordinate 5 j) = none then some (yCoordinate 5 j) else none

private def rootMass5 (h : HistoryN 5) (c : CoordinateN 5) : ℕ :=
  ∑ j : Fin 5, if residualRoot5 j h = some c then 1 else 0

private def totalRootMass5 (h : HistoryN 5) : ℕ :=
  ∑ c : CoordinateN 5, rootMass5 h c

private def cumulativeRootMass5 (h : HistoryN 5) (c : CoordinateN 5) : ℕ :=
  ∑ d : CoordinateN 5, if d ≤ c then rootMass5 h d else 0

private noncomputable def proportionalRootChoice5
    (h : HistoryN 5) (u : Fin 60) : Option (CoordinateN 5) := by
  classical
  by_cases ht : totalRootMass5 h = 0
  · exact none
  · let q : ℕ := u.1 * totalRootMass5 h / 60
    let candidates :=
      Finset.univ.filter (fun c : CoordinateN 5 =>
        rootMass5 h c > 0 ∧ q < cumulativeRootMass5 h c)
    by_cases hc : candidates.Nonempty
    · exact some (candidates.min' hc)
    · exact none

private def proportionalRootLaw5 (h : HistoryN 5) : Prop :=
  totalRootMass5 h ≠ 0 →
    ∀ c : CoordinateN 5,
      ((Finset.univ.filter
          (fun u : Fin 60 => proportionalRootChoice5 h u = some c)).card : ℚ) / 60 =
        (rootMass5 h c : ℚ) / totalRootMass5 h

private def randomPolicyLegal5 : Prop :=
  ∀ (h : HistoryN 5) (u : Fin 60) (c : CoordinateN 5),
    proportionalRootChoice5 h u = some c → h c = none

private noncomputable def target5 (ω : OracleN 5) : ℝ := targetN 5 ω

private def targetMeasurable5 (h : HistoryN 5) : Prop :=
  ∀ (ω ω' : OracleN 5),
    consistentN h ω → consistentN h ω' → target5 ω = target5 ω'

abbrev Seed5 := Fin 11 → Fin 60

structure Transcript5 where
  order : List (CoordinateN 5)
  history : HistoryN 5

private def initialTranscript5 : Transcript5 :=
  { order := [], history := emptyHistoryN 5 }

private noncomputable def randomTranscript5
    (seed : Seed5) (ω : OracleN 5) : ℕ → Transcript5
  | 0 => initialTranscript5
  | m + 1 =>
      let t := randomTranscript5 seed ω m
      letI := Classical.propDecidable (targetMeasurable5 t.history)
      if targetMeasurable5 t.history then
        t
      else
        match proportionalRootChoice5 t.history
            (seed ⟨m % 11, Nat.mod_lt _ (by norm_num)⟩) with
        | none => t
        | some c =>
            { order := t.order ++ [c]
              history := revealN t.history c ω }

private noncomputable def jointFiber5
    (m : ℕ) (t : Transcript5) : Finset (OracleN 5 × Seed5) := by
  classical
  exact Finset.univ.filter (fun z => randomTranscript5 z.2 z.1 m = t)

private noncomputable def jointPosteriorVariance5
    (f : OracleN 5 → ℝ) (m : ℕ) (t : Transcript5) : ℝ :=
  let S := jointFiber5 m t
  if S.Nonempty then
    let q : ℝ := S.card
    (∑ z ∈ S, (f z.1) ^ 2) / q - ((∑ z ∈ S, f z.1) / q) ^ 2
  else
    0

private noncomputable def randomizedArea5 (f : OracleN 5 → ℝ) : ℝ :=
  ∑ m : Fin 12,
    (∑ z : OracleN 5 × Seed5,
      jointPosteriorVariance5 f m.1 (randomTranscript5 z.2 z.1 m.1)) /
      (Fintype.card (OracleN 5 × Seed5) : ℝ)

/-- Exact finite-product formalization of the common-coordinate claim and its obstruction. -/
def claim60095 : Prop :=
  (∀ n : ℕ, 2 ≤ n →
    LegalPolicyN (legalPolicyN n) ∧
    (∀ j : Fin n, (treeN n j).depth ≤ 2) ∧
    rootInclusiveAreaN n (legalPolicyN n) (targetN n) =
      (13 * (n : ℝ) + 23) / (16 * (n : ℝ)) ∧
    rootInclusiveAreaN n (legalPolicyN n) (targetN n) ≤ 49 / 32 ∧
    (49 / 32 : ℝ) < 2) ∧
  (∀ h : HistoryN 5, proportionalRootLaw5 h) ∧
  randomPolicyLegal5 ∧
  randomizedArea5 target5 = (291101767 : ℝ) / 144000000 ∧
  randomizedArea5 target5 = 2 + (3101767 : ℝ) / 144000000 ∧
  (2 : ℝ) < randomizedArea5 target5 ∧
  (∃ p : CoordinatePolicyN 5,
    LegalPolicyN p ∧
      rootInclusiveAreaN 5 p target5 = (11 : ℝ) / 10)

end MathlibPlus.Open.OracleArea.Claim60095
