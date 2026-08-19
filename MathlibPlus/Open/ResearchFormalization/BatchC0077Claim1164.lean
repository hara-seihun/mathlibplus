import MathlibPlus.Open.C0079NeighboringMinor

namespace MathlibPlus.Open.ResearchFormalization.BatchC0077

open scoped BigOperators
open MathlibPlus.Open.C0079

noncomputable section

/-- The row set for `K_(1)`. -/
def oneRows1164 (d : ℕ) : Fin d → Fin (2 * d) :=
  fun i =>
    if h : i.1 = d - 1 then
      ⟨d, by omega⟩
    else
      ⟨i.1, by omega⟩

/-- The row set for `K_(2)`, available from `d ≥ 2`. -/
def twoRows1164 (d : ℕ) (hd : 2 ≤ d) : Fin d → Fin (2 * d) :=
  fun i =>
    if h : i.1 = d - 1 then
      ⟨d + 1, by omega⟩
    else
      ⟨i.1, by omega⟩

/-- The row set for `K_(1,1)`, available from `d ≥ 2`. -/
def oneOneRows1164 (d : ℕ) (hd : 2 ≤ d) : Fin d → Fin (2 * d) :=
  fun i =>
    if h : d - 2 ≤ i.1 then
      ⟨i.1 + 1, by omega⟩
    else
      ⟨i.1, by omega⟩

/-- A flagged minor for one of the displayed row sets. -/
def flaggedMinor1164 (d : ℕ) (a : ℝ)
    (rows : Fin d → Fin (2 * d)) : ℝ :=
  Matrix.det (fun i j => flaggedArray d a (rows i) j)

/-- The four gauged area-at-most-two cup coordinates. -/
def alphaEmpty1164 (d : ℕ) (a : ℝ) : ℝ :=
  emptyMinor d a

def alphaOne1164 (d : ℕ) (a : ℝ) : ℝ :=
  emptyMinor d a - flaggedMinor1164 d a (oneRows1164 d)

def alphaTwo1164 (d : ℕ) (hd : 2 ≤ d) (a : ℝ) : ℝ :=
  emptyMinor d a - flaggedMinor1164 d a (oneRows1164 d) +
    flaggedMinor1164 d a (twoRows1164 d hd)

def alphaOneOne1164 (d : ℕ) (hd : 2 ≤ d) (a : ℝ) : ℝ :=
  emptyMinor d a - flaggedMinor1164 d a (oneRows1164 d) +
    flaggedMinor1164 d a (oneOneRows1164 d hd)

/-- The sign assertions for all four coordinates available at a fixed `d`.
For `d = 1` the last two coordinates are absent. -/
def availableAreaTwoSigns1164 (d : ℕ) (a : ℝ) : Prop :=
  (1 / 2 < a →
    0 < alphaEmpty1164 d a ∧
    0 < alphaOne1164 d a ∧
    (∀ hd : 2 ≤ d,
      0 < alphaTwo1164 d hd a ∧
      0 < alphaOneOne1164 d hd a)) ∧
  (a = 1 / 2 →
    0 ≤ alphaEmpty1164 d a ∧
    0 ≤ alphaOne1164 d a ∧
    (∀ hd : 2 ≤ d,
      0 ≤ alphaTwo1164 d hd a ∧
      0 ≤ alphaOneOne1164 d hd a))

/-- Claim 1164: every available area-at-most-two gauged cup coordinate has the
stated positive/boundary sign in rank `r ≥ 2` (`d = r - 1`), while the `(1)`
coordinate is negative below `a = 1/2`, including rank two and every `d ≥ 1`. -/
def areaTwoPositivitySharpThreshold_claim1164 : Prop :=
  (∀ r : ℕ, 2 ≤ r → ∀ a : ℝ,
    availableAreaTwoSigns1164 (r - 1) a) ∧
  (∀ a : ℝ, 0 < a → a < 1 / 2 → alphaOne1164 1 a < 0) ∧
  (∀ d : ℕ, 1 ≤ d → ∀ a : ℝ,
    0 < a → a < 1 / 2 → alphaOne1164 d a < 0)

end

end MathlibPlus.Open.ResearchFormalization.BatchC0077
