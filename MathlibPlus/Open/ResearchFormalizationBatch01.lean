import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalizationBatch

abbrev PositiveNat := {n : ℕ // 0 < n}

noncomputable def bdMu (n : PositiveNat) : ℝ :=
  (ArithmeticFunction.moebius n.1 : ℤ)

noncomputable def bdCoefficient (k : ℕ) : ℂ :=
  ∑ j ∈ Finset.range (k + 1),
    (-1 : ℂ) ^ j * (Nat.choose k j : ℂ) /
      riemannZeta ((2 * j + 2 : ℕ) : ℂ)

noncomputable def bdMöbiusCoefficient (k : ℕ) : ℂ :=
  ∑' n : PositiveNat,
    (ArithmeticFunction.moebius n.1 : ℂ) / (n.1 : ℂ) ^ 2 *
      (1 - (n.1 : ℂ) ^ (-2 : ℤ)) ^ k

def claim9414 : Prop :=
  ∀ k : ℕ, bdCoefficient k = bdMöbiusCoefficient k

noncomputable def bdQ (x : ℝ) : ℝ :=
  Real.exp (-x) * ∑' k : ℕ,
    Complex.normSq (bdCoefficient k) * x ^ k / (Nat.factorial k : ℝ)

noncomputable def bdQDoubleSeries (x : ℝ) : ℝ :=
  ∑' m : PositiveNat, ∑' n : PositiveNat,
    bdMu m * bdMu n /
        ((m.1 : ℝ) ^ 2 * (n.1 : ℝ) ^ 2) *
      Real.exp
        (-x * ((m.1 : ℝ) ^ (-2 : ℤ) + (n.1 : ℝ) ^ (-2 : ℤ) -
          ((m.1 * n.1 : ℕ) : ℝ) ^ (-2 : ℤ)))

def claim9417 : Prop :=
  ∀ x : ℝ, bdQ x = bdQDoubleSeries x

noncomputable def bdChannel (r : ℕ) (x : ℝ) : ℝ :=
  ∑' n : PositiveNat,
    bdMu n * (n.1 : ℝ) ^ (-(2 * r + 2 : ℤ)) *
      Real.exp (-x * (n.1 : ℝ) ^ (-2 : ℤ))

noncomputable def bdChannelRhs (x : ℝ) : ℝ :=
  ∑' r : ℕ, x ^ r / (Nat.factorial r : ℝ) *
    (bdChannel r x) ^ 2

def claim9418 : Prop :=
  (∀ x : ℝ, bdQ x = bdChannelRhs x) ∧
    (∀ (r : ℕ) (x : ℝ), 0 ≤ x →
      0 ≤ x ^ r / (Nat.factorial r : ℝ) * (bdChannel r x) ^ 2)

noncomputable def bdRiesz (x : ℝ) : ℝ :=
  x * bdChannel 0 x

noncomputable def bdHigherChannels (x : ℝ) : ℝ :=
  ∑' r : PositiveNat, x ^ r.1 / (Nat.factorial r.1 : ℝ) *
    (bdChannel r.1 x) ^ 2

def claim9419 : Prop :=
  ∀ x : ℝ, x ≠ 0 →
    bdQ x = |bdRiesz x| ^ 2 / x ^ 2 + bdHigherChannels x

noncomputable def bdInnerBound (x : ℝ) : ℝ :=
  ∑' n : PositiveNat,
    (n.1 : ℝ) ^ (-4 : ℤ) *
      Real.exp (-x * (n.1 : ℝ) ^ (-2 : ℤ) / 2)

def claim9420 : Prop :=
  (∀ x : ℝ, 1 ≤ x →
    0 ≤ bdQ x - |bdRiesz x| ^ 2 / x ^ 2 ∧
      bdQ x - (bdChannel 0 x) ^ 2 ≤ x * (bdInnerBound x) ^ 2) ∧
  (∃ C X : ℝ, 0 < C ∧ 0 < X ∧
    ∀ x : ℝ, X ≤ x → bdInnerBound x ≤ C * x ^ (-3 / 2 : ℝ)) ∧
  (∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 1 ≤ x →
    bdQ x - |bdRiesz x| ^ 2 / x ^ 2 ≤ C * x ^ (-2 : ℝ))

end MathlibPlus.Open.ResearchFormalizationBatch
