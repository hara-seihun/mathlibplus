import Mathlib

namespace MathlibPlus.Open.Analysis.FormalizationBatchMellin

open Asymptotics Filter MeasureTheory Set Topology
open scoped BigOperators

noncomputable section

/-- Euler/logarithmic differentiation. -/
def eulerDerivative (f : ℝ → ℝ) : ℝ → ℝ := fun r => r * deriv f r

def eulerDerivativeN (j : ℕ) (f : ℝ → ℝ) : ℝ → ℝ :=
  (eulerDerivative^[j]) f

def rapidlyDecreasing (f : ℝ → ℝ) : Prop :=
  ∀ m : ℕ,
    IsBigO atTop f (fun r : ℝ => Real.rpow (1 + r) (-(m : ℝ)))

def smoothFixedProfile (w : ℝ → ℝ) : Prop :=
  ∃ (c : ℝ) (v : ℝ → ℝ) (η : ℝ),
    0 < η ∧
      ContDiffOn ℝ ⊤ v (Set.Ioi 0) ∧
      (∀ r : ℝ, 0 < r → w r = c * Real.exp (-r) + v r) ∧
      (∀ j : ℕ, ∃ C : ℝ,
        IsBigOWith C (nhdsWithin 0 (Set.Ioi 0))
          (eulerDerivativeN j v) (fun r : ℝ => Real.rpow r η)) ∧
      (∀ j : ℕ, rapidlyDecreasing (eulerDerivativeN j v))

def realMellin (w : ℝ → ℝ) (z : ℂ) : ℂ :=
  ∫ r : ℝ,
    ((w r : ℂ) * Complex.exp ((z - 1) * (Real.log r : ℂ))) ∂
      (volume.restrict (Set.Ioi 0))

def compactProfileZero (r : ℝ) : ℝ :=
  if 0 < r ∧ r ≤ 1 then 1 else 0

def compactProfile (m : ℕ) (r : ℝ) : ℝ :=
  if m = 0 then compactProfileZero r else max (1 - r) 0 ^ m

def rationalMellin (m : ℕ) (z : ℂ) : ℂ :=
  (Nat.factorial m : ℂ) /
    Finset.prod (Finset.range (m + 1)) (fun k => z + (k : ℂ))


def claim_13747 : Prop :=
  (∀ r : ℝ,
    compactProfile 0 r = if 0 < r ∧ r ≤ 1 then 1 else 0) ∧
    (∀ m : ℕ, 1 ≤ m → ∀ r : ℝ,
      compactProfile m r = max (1 - r) 0 ^ m) ∧
    (∀ m : ℕ, ∀ z : ℂ, 0 < z.re →
      realMellin (compactProfile m) z = rationalMellin m z) ∧
    (∀ m : ℕ, ∀ a b : ℝ, 0 < a → a ≤ b →
      ∃ C T : ℝ, 0 ≤ C ∧ 0 ≤ T ∧
        ∀ σ t : ℝ, a ≤ σ → σ ≤ b → T ≤ |t| →
          ‖realMellin (compactProfile m)
              ((σ : ℂ) + Complex.I * (t : ℂ))‖ ≤
            C * Real.rpow (1 + |t|) (-(m + 1 : ℝ)))


def abelTransform (F : ℝ → ℝ) (N₀ lam : ℝ) : ℝ :=
  lam * ∫ N : ℝ, F N * Real.rpow N (-lam - 1) ∂
    (volume.restrict (Set.Ici N₀))

def claim_13757 : Prop :=
  ∀ (F : ℝ → ℝ) (N₀ : ℝ), 0 < N₀ →
    (∃ B : ℝ, 0 ≤ B ∧ ∀ N : ℝ, |F N| ≤ B) →
    ∀ L : ℝ,
      Tendsto (fun lam : ℝ => abelTransform F N₀ lam)
        (nhdsWithin 0 (Set.Ioi 0)) (𝓝 L) →
      |L| ≤ limsup (fun N : ℝ => |F N|) atTop


def complexMellin (h : ℝ → ℂ) (s : ℂ) : ℂ :=
  ∫ y : ℝ,
    h y * Complex.exp (-(s + 1) * (Real.log y : ℂ)) ∂
      (volume.restrict (Set.Ioi 0))

def criticalLineMellin (h : ℝ → ℂ) (t : ℝ) : ℂ :=
  complexMellin h ((1 / 2 : ℂ) + Complex.I * (t : ℂ))

def logarithmicFourierPacket (h : ℝ → ℂ) (t : ℝ) : ℂ :=
  ∫ x : ℝ,
    Complex.exp (-(x : ℂ) / 2) * h (Real.exp x) *
      Complex.exp (-Complex.I * (t : ℂ) * (x : ℂ))

def criticalLineMeasure : Measure ℝ :=
  ENNReal.ofReal (1 / (2 * Real.pi)) • volume

def claim_13758 : Prop :=
  (∀ (G : ℝ → ℂ), MemLp G 2 criticalLineMeasure →
    ∀ ε : ℝ, 0 < ε →
      ∃ h : ℝ → ℂ,
        ContDiff ℝ ⊤ h ∧
          HasCompactSupport h ∧
          (∀ y : ℝ, y ≤ 0 → h y = 0) ∧
          eLpNorm (fun t : ℝ => G t - criticalLineMellin h t) 2
              criticalLineMeasure < ENNReal.ofReal ε) ∧
    (∀ h : ℝ → ℂ, ContDiff ℝ ⊤ h → HasCompactSupport h →
      (∀ y : ℝ, y ≤ 0 → h y = 0) →
      ∀ t : ℝ,
        criticalLineMellin h t = logarithmicFourierPacket h t)

end

end MathlibPlus.Open.Analysis.FormalizationBatchMellin
