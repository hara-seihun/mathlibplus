import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.NR2Formalization.Repair

/-- Squarefreeness in the prime-divisor form used by the toggle graph. -/
def nr2Squarefree (n : ℕ) : Prop :=
  ∀ p : ℕ, Nat.Prime p → ¬ p ^ 2 ∣ n

noncomputable def nr2PrimeDivisors (m : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range (m + 1)).filter (fun p => Nat.Prime p ∧ p ∣ m)

noncomputable def nr2Mobius (n : ℕ) : ℤ := by
  classical
  exact if n = 0 then 0 else
    if nr2Squarefree n then
      if Even (nr2PrimeDivisors n).card then 1 else -1
    else 0

noncomputable def oneToggleVertices (X : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range (X + 1)).filter nr2Squarefree

def oneToggleEdge (n m : ℕ) : Prop :=
  ∃ p : ℕ, Nat.Prime p ∧ (m = n * p ∨ n = m * p)

noncomputable def oneToggleCovered (M : Finset (ℕ × ℕ)) : Finset ℕ :=
  M.biUnion (fun e => {e.1, e.2})

def oneToggleMatching (X : ℕ) (M : Finset (ℕ × ℕ)) : Prop :=
  (∀ e ∈ M,
    e.1 ∈ oneToggleVertices X ∧ e.2 ∈ oneToggleVertices X ∧
      e.1 < e.2 ∧ oneToggleEdge e.1 e.2 ∧
      nr2Mobius e.1 = -nr2Mobius e.2) ∧
    (∀ e ∈ M, ∀ f ∈ M, e ≠ f →
      e.1 ≠ f.1 ∧ e.1 ≠ f.2 ∧ e.2 ≠ f.1 ∧ e.2 ≠ f.2)

noncomputable def oneToggleDeficiency (X : ℕ) (M : Finset (ℕ × ℕ)) : ℕ :=
  (oneToggleVertices X).card - (oneToggleCovered M).card

def claim10656 : Prop :=
  ∀ X : ℕ, ∀ n m : ℕ,
    n ∈ oneToggleVertices X → m ∈ oneToggleVertices X →
      (oneToggleEdge n m ↔
        ∃ p : ℕ, Nat.Prime p ∧ (m = n * p ∨ n = m * p)) ∧
      (oneToggleEdge n m → nr2Mobius n = -nr2Mobius m)

def claim10659 : Prop :=
  let X : ℕ := 300000
  let V := oneToggleVertices X
  let plus := V.filter (fun n => nr2Mobius n = 1)
  let minus := V.filter (fun n => nr2Mobius n = -1)
  (Nat.dist plus.card minus.card = 220) ∧
    (50132 - 220 = 49912) ∧
    (∃ M : Finset (ℕ × ℕ),
      oneToggleMatching X M ∧
      (∀ M' : Finset (ℕ × ℕ), oneToggleMatching X M' →
        (oneToggleCovered M').card ≤ (oneToggleCovered M).card) ∧
      oneToggleDeficiency X M = 50132) ∧
    (∀ M : Finset (ℕ × ℕ), oneToggleMatching X M →
      220 ≤ oneToggleDeficiency X M)

def claim10660 : Prop :=
  let X : ℕ := 300000
  (∀ M : Finset (ℕ × ℕ), oneToggleMatching X M →
    50132 ≤ oneToggleDeficiency X M) ∧
    50132 > X / 6

end MathlibPlus.Open.NR2Formalization.Repair
