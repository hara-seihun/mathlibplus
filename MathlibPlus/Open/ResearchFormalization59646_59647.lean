import Mathlib

namespace MathlibPlus.Open

/-- Strict increase of a natural-number sequence on the ranks 2 through 7. -/
def strictlyIncreasingRanks2Through7 (f : ℕ → ℕ) : Prop :=
  ∀ ⦃i j : ℕ⦄,
    2 ≤ i → i ≤ 7 → 2 ≤ j → j ≤ 7 → i < j → f i < f j

/-- The exact continuation data described in admitted claim 59646. -/
def rankEightContinuation59646
    (A B : ℕ) (m : ℕ → ℚ) (μ q qμ : ℕ → ℕ) : Prop :=
  m 2 = ((1 : ℚ) / 2) ∧
  m 3 = 2 ∧
  m 4 = 24 ∧
  m 5 = 1152 ∧
  m 6 = 276480 ∧
  m 7 = 398131200 ∧
  μ 2 = 1 ∧
  μ 3 = 1 ∧
  μ 4 = 2 ∧
  μ 5 = 6 ∧
  μ 6 = 24 ∧
  μ 7 = 120 ∧
  (∀ r : ℕ, 3 ≤ r → r ≤ 7 →
    m r = (2 : ℚ) * (Nat.factorial (r - 1) : ℚ) * m (r - 1)) ∧
  (∀ r : ℕ, 2 ≤ r → r ≤ 7 →
    m (r + 1) = (q r : ℚ) * m r ∧
    μ (r + 1) = qμ r * μ r) ∧
  (∀ r : ℕ, 2 ≤ r → r ≤ 7 → 0 < q r ∧ 0 < qμ r) ∧
  strictlyIncreasingRanks2Through7 q ∧
  strictlyIncreasingRanks2Through7 qμ ∧
  q 7 = A ∧
  qμ 7 = B ∧
  m 8 = (A : ℚ) * 398131200 ∧
  μ 8 = 120 * B

/-- The rank-eight values realized by the continuations in admitted claim 59646. -/
def rankEightValues59646 : Set (ℚ × ℕ) :=
  {p | ∃ A B : ℕ,
    A > 1440 ∧ B > 5 ∧
    ∃ m : ℕ → ℚ, ∃ μ q qμ : ℕ → ℕ,
      rankEightContinuation59646 A B m μ q qμ ∧ p = (m 8, μ 8)}

/-- Finite-range parametric rank-eight continuation claim 59646. -/
def claim59646 : Prop :=
  (∀ A B : ℕ, A > 1440 → B > 5 →
    ∃ m : ℕ → ℚ, ∃ μ q qμ : ℕ → ℕ,
      rankEightContinuation59646 A B m μ q qμ) ∧
  Set.Infinite rankEightValues59646

/-- The exact continuation data described in admitted claim 59647. -/
def rankEightContinuation59647
    (A B : ℕ) (m : ℕ → ℚ) (μ q qμ : ℕ → ℕ) : Prop :=
  m 2 = ((1 : ℚ) / 2) ∧
  m 3 = 2 ∧
  m 4 = 24 ∧
  m 5 = 1152 ∧
  m 6 = 276480 ∧
  m 7 = 398131200 ∧
  μ 2 = 1 ∧
  μ 3 = 1 ∧
  μ 4 = 2 ∧
  μ 5 = 6 ∧
  μ 6 = 24 ∧
  μ 7 = 120 ∧
  q 2 = 4 ∧
  q 3 = 12 ∧
  q 4 = 48 ∧
  q 5 = 240 ∧
  q 6 = 1440 ∧
  q 7 = A ∧
  qμ 2 = 1 ∧
  qμ 3 = 2 ∧
  qμ 4 = 3 ∧
  qμ 5 = 4 ∧
  qμ 6 = 5 ∧
  qμ 7 = B ∧
  (∀ r : ℕ, 2 ≤ r → r ≤ 7 →
    m (r + 1) = (q r : ℚ) * m r ∧
    μ (r + 1) = qμ r * μ r) ∧
  strictlyIncreasingRanks2Through7 q ∧
  strictlyIncreasingRanks2Through7 qμ ∧
  m 8 > (2 : ℚ) * (Nat.factorial 7 : ℚ) * m 7 ∧
  μ 8 > Nat.factorial 6

/-- The rank-eight values realized by the continuations in admitted claim 59647. -/
def rankEightValues59647 : Set (ℚ × ℕ) :=
  {p | ∃ A B : ℕ,
    10081 ≤ A ∧ 7 ≤ B ∧
    ∃ m : ℕ → ℚ, ∃ μ q qμ : ℕ → ℕ,
      rankEightContinuation59647 A B m μ q qμ ∧ p = (m 8, μ 8)}

/-- Parametric rank-eight obstruction claim 59647. -/
def claim59647 : Prop :=
  (∀ A B : ℕ, 10081 ≤ A → 7 ≤ B →
    ∃ m : ℕ → ℚ, ∃ μ q qμ : ℕ → ℕ,
      rankEightContinuation59647 A B m μ q qμ) ∧
  Set.Infinite rankEightValues59647

end MathlibPlus.Open
