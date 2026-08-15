import Mathlib

namespace MathlibPlus.Open.CriticalLine

abbrev Vec2 := Fin 2 → ℝ

def criticalBlock (c : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![ (0 : ℝ), -1; 1, -2 * c ]

def blockConditions (c m ε : ℝ) (Q : Vec2 → ℝ) : Prop :=
  (∀ (a : ℝ) (x : Vec2), Q (a • x) = a ^ 2 * Q x) ∧
  (∀ x : Vec2, m * ‖x‖ ^ 2 ≤ Q x) ∧
  (∀ x : Vec2,
    |Q (Matrix.mulVec (criticalBlock c) x) - Q x| ≤ ε * ‖x‖ ^ 2)

def criticalLineSupercriticalCoboundaryLowerBound : Prop :=
  (∀ (c m ε : ℝ) (Q : Vec2 → ℝ),
    1 < c → 0 < m → blockConditions c m ε Q →
      ε ≥ m * ((c + Real.sqrt (c ^ 2 - 1)) ^ 2 - 1)) ∧
  (∀ {ι : Type} (c : ι → ℝ) (Q : ι → Vec2 → ℝ) (m ε : ℝ),
    0 < m →
    (∀ i, blockConditions (c i) m ε (Q i)) →
    ((∀ i, 1 < c i →
        m * ((c i + Real.sqrt ((c i) ^ 2 - 1)) ^ 2 - 1) ≤ ε) ∧
      ((∀ R : ℝ, ∃ i, R < c i) → False)))

end MathlibPlus.Open.CriticalLine
