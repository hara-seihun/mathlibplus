import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.Research

noncomputable section

open Classical

/-- The threshold ratio and its canonical root in the admitted (2,3) interval. -/
def constantPhaseRatio (ξ : ℝ) : ℝ :=
  3 + ξ⁻¹ + Real.log ξ - 2 * ξ

def criticalXi : ℝ :=
  sInf {x : ℝ | x ∈ Set.Icc (2 : ℝ) 3 ∧ constantPhaseRatio x = 0}

def constantPhaseA (ξ : ℝ) : ℝ :=
  (1 + ξ⁻¹ + Real.log ξ) / (ξ - 1)

def constantPhasePhi (ξ u : ℝ) : ℝ :=
  1 + Real.log u - constantPhaseA ξ * (u - 1)

def admissiblePhaseWeight (ξ : ℝ) (w : ℝ → ℝ) : Prop :=
  ContDiffOn ℝ 1 w (Set.Icc (1 : ℝ) ξ) ∧
    (∀ u ∈ Set.Icc (1 : ℝ) ξ, 0 ≤ w u) ∧
    (∫ u in (1 : ℝ)..ξ, w u) = 1

def constantPhaseJ (ξ : ℝ) (w : ℝ → ℝ) : ℝ :=
  w ξ / ξ + w 1
    + ∫ u in (1 : ℝ)..ξ, w u / u
    + ∫ u in (1 : ℝ)..ξ, |deriv w u| / u

/-- Constant-phase obstacle dual and its integration-by-parts lower bound. -/
def claim2006 : Prop :=
  ∀ (ξ : ℝ), 1 < ξ → ξ ≤ criticalXi →
    constantPhasePhi ξ 1 = 1 ∧
      constantPhasePhi ξ ξ = -ξ⁻¹ ∧
      (∀ u ∈ Set.Icc (1 : ℝ) ξ,
        |constantPhasePhi ξ u| ≤ 1 / u) ∧
      (∀ u ∈ Set.Ioo (1 : ℝ) ξ,
        |constantPhasePhi ξ u| < 1 / u) ∧
      ∀ w : ℝ → ℝ,
        admissiblePhaseWeight ξ w → constantPhaseJ ξ w ≥ constantPhaseA ξ
/-- Exact-S0 source predicate. -/
def claim3640 (q : ℝ → ℝ) : Prop :=
  (∀ x : ℝ, q (-x) = q x) ∧
    ContDiff ℝ ⊤ q ∧
    HasCompactSupport q ∧
    q 0 = 0 ∧
    (∫ x : ℝ, q x) = 0
/-- The Riesz field on the positive real carrier. -/
def rieszField (x : ℝ) : ℝ :=
  x * ∑' n : ℕ,
    if 0 < n then
      (ArithmeticFunction.moebius n : ℝ) / (n : ℝ) ^ 2
        * Real.exp (-x / (n : ℝ) ^ 2)
    else 0

def criticalLogG (u : ℝ) : ℝ :=
  Real.exp (-u / 2) * rieszField (Real.exp (2 * u))

def criticalLogH (u : ℝ) : ℝ :=
  Real.exp (3 * u / 2 - Real.exp (2 * u))

/-- Critical-log renewal equation after the admitted reciprocal-square substitution. -/
def claim9328 : Prop :=
  ∀ u : ℝ,
    (∑' m : ℕ,
      if 0 < m then
        Real.rpow (m : ℝ) (-1 / 2) * criticalLogG (u - Real.log (m : ℝ))
      else 0) = criticalLogH u

end

end MathlibPlus.Open.Research
