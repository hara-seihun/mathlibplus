import Mathlib

namespace MathlibPlus.Open.Research

open scoped BigOperators

noncomputable section

structure FinitePartition (C : Type*) where
  cells : Finset (Finset C)
  nonempty : ∀ s, s ∈ cells → s.Nonempty
  disjoint : ∀ s, s ∈ cells → ∀ t, t ∈ cells → s ≠ t → Disjoint s t
  cover : ∀ x : C, ∃ s, s ∈ cells ∧ x ∈ s

noncomputable def partitionCell {C : Type*} (P : FinitePartition C) (x : C) : Finset C :=
  Classical.choose (P.cover x)

def partitionCellDiameter {C : Type*} (rho : C → C → ℝ)
    (s : Finset C) : ℝ :=
  sSup {z : ℝ | ∃ x ∈ s, ∃ y ∈ s, z = rho x y}

def partitionSequenceValid {C : Type*} [Fintype C]
    (P : ℕ → FinitePartition C) : Prop :=
  (P 0).cells.card = 1 ∧
    ∀ n : ℕ, 0 < n → (P n).cells.card ≤ 2 ^ (2 ^ n)

def partitionSequenceCost {C : Type*} [Fintype C]
    (rho : C → C → ℝ) (P : ℕ → FinitePartition C) : ℝ :=
  sSup {z : ℝ | ∃ x : C,
    z = ∑' n : ℕ,
      Real.rpow 2 ((n : ℝ) / 2) *
        partitionCellDiameter rho (partitionCell (P n) x)}

def gammaTwo {C : Type*} [Fintype C]
    (rho : C → C → ℝ) : ℝ :=
  sInf {z : ℝ | ∃ P : ℕ → FinitePartition C,
    partitionSequenceValid P ∧ partitionSequenceCost rho P = z}

def ultrametricPredicate {C : Type*} (rho : C → C → ℝ) : Prop :=
  (∀ x, rho x x = 0) ∧
    (∀ x y, rho x y = rho y x) ∧
    (∀ x y, 0 ≤ rho x y) ∧
    (∀ x y, rho x y = 0 → x = y) ∧
    (∀ x y z, rho x z ≤ max (rho x y) (rho y z))

def firstTranscriptDifference {d : ℕ} {C : Type*}
    (A : Fin d → Type) (code : C → ∀ i : Fin d, A i)
    (x y : C) : Fin (d + 1) := by
  classical
  by_cases h : ∃ i, code x i ≠ code y i
  · let differing := Finset.univ.filter (fun i : Fin d => code x i ≠ code y i)
    have hdiffering : differing.Nonempty := by
      rcases h with ⟨i, hi⟩
      exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
    exact ⟨(differing.min' hdiffering).1,
      Nat.lt_succ_of_lt (differing.min' hdiffering).2⟩
  · exact 0

def transcriptUltrametric {d : ℕ} {C : Type*}
    (A : Fin d → Type) (code : C → ∀ i : Fin d, A i)
    (r : Fin (d + 1) → ℝ) (x y : C) : ℝ := by
  classical
  exact if x = y then 0 else r (firstTranscriptDifference A code x y)

def leastBranchExponent (b : ℕ) : ℕ := by
  classical
  exact if h : ∃ q : ℕ, 0 < q ∧ b ≤ 2 ^ q then Nat.find h else 1

def chainRadius {d : ℕ} (r : Fin (d + 1) → ℝ) (q n : ℕ) : ℝ :=
  if n = 0 then r 0 else r ⟨min d (2 ^ n / q), by omega⟩

def dyadicChainRadii {d : ℕ} (r : Fin (d + 1) → ℝ) : Prop :=
  ∀ i : Fin d, r (Fin.castSucc i) = Real.rpow 2 (-(i.1 : ℝ))

/-- Bounded-branch transcript majorizing-chain theorem. -/
def claim_59778 : Prop :=
  ∀ (d b : ℕ), 1 ≤ d → 2 ≤ b →
    ∀ (A : Fin d → Type) [∀ i, Fintype (A i)],
    ∀ (C : Type) [Fintype C], Nonempty C →
    ∀ (code : C → ∀ i : Fin d, A i), Function.Injective code →
    (∀ i : Fin d, Fintype.card (A i) ≤ b) →
    ∀ (r : Fin (d + 1) → ℝ),
      (∀ i : Fin d, r (Fin.castSucc i) > r (Fin.succ i)) →
      r (Fin.last d) = 0 →
      let rho := transcriptUltrametric A code r
      let q := leastBranchExponent b
      ultrametricPredicate rho ∧
        gammaTwo rho ≤
          r 0 + ∑' n : ℕ,
            (if 0 < n then
              Real.rpow 2 ((n : ℝ) / 2) * chainRadius r q n
            else 0) ∧
        (dyadicChainRadii r →
          gammaTwo rho ≤ 6 * Real.sqrt (q : ℝ))

end
end MathlibPlus.Open.Research
