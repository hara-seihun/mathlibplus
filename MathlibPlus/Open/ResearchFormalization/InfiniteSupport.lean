import Mathlib

namespace MathlibPlus.Open.ResearchFormalization

noncomputable section

/-- The positive-integer pair fixture used for the infinite-support boundary. -/
abbrev PositiveIndex := {n : ℕ // 0 < n}

def eCell (n : PositiveIndex) : PositiveIndex × Bool := (n, true)
def fCell (n : PositiveIndex) : PositiveIndex × Bool := (n, false)

def firstFixtureRow (p : PositiveIndex × Bool) : ℝ :=
  if p.2 then 1 / (p.1.1 : ℝ) else 0

def secondFixtureRow (p : PositiveIndex × Bool) : ℝ :=
  if p.2 then 0 else 1

def lexAbovePair (a₁ a₂ b₁ b₂ : ℝ) : Prop :=
  b₁ < a₁ ∨ (b₁ = a₁ ∧ b₂ < a₂)

def fixtureAggregateDifference (N₁ N₂ : ℕ) (n : PositiveIndex) : ℝ :=
  (N₁ : ℝ) / (n.1 : ℝ) - N₂

/-- The lexicographic stack wins on every pair, while each fixed positive
integer aggregate eventually reverses every pair. -/
def claim51599 : Prop :=
  (∀ n : PositiveIndex,
    lexAbovePair (firstFixtureRow (eCell n)) (secondFixtureRow (eCell n))
      (firstFixtureRow (fCell n)) (secondFixtureRow (fCell n))) ∧
    ∀ N₁ N₂ : ℕ, 0 < N₁ → 0 < N₂ →
      ∃ n₀ : PositiveIndex, ∀ n : PositiveIndex, n₀ ≤ n →
        fixtureAggregateDifference N₁ N₂ n < 0

end

end MathlibPlus.Open.ResearchFormalization
