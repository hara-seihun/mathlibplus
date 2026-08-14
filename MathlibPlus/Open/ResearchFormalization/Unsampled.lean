import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.Unsampled

noncomputable section

open Filter Set MeasureTheory
open scoped BigOperators Topology

/-- The exact support condition for an unsampled compact source. -/
def unsampledSources (c : ℝ) : Set (ℝ → ℝ) :=
  {h |
    ContDiff ℝ ⊤ h ∧ Even h ∧ HasCompactSupport h ∧
      Function.support h ⊆ Ioo (-1 / c) 0 ∪ Ioo 0 (1 / c) ∧
      (∫ z : ℝ, h z) = 0}

def exactS0 : Set (ℝ → ℝ) :=
  {h | h 0 = 0 ∧ (∫ z : ℝ, h z) = 0}

def InfiniteDimensionalSet (S : Set (ℝ → ℝ)) : Prop :=
  ∀ n : ℕ, ∃ v : Fin n → (ℝ → ℝ),
    (∀ i, v i ∈ S) ∧ LinearIndependent ℝ v

/-- `𝒰_c` is the stated real smooth even compactly supported zero-integral
source space. -/
def claim_12439 : Prop :=
  ∀ c : ℝ, 1 < c →
    ∀ h : ℝ → ℝ,
      h ∈ unsampledSources c ↔
        (ContDiff ℝ ⊤ h ∧ Even h ∧ HasCompactSupport h ∧
          Function.support h ⊆ Ioo (-1 / c) 0 ∪ Ioo 0 (1 / c) ∧
          (∫ z : ℝ, h z) = 0)

/-- At frequency zero the Fourier transform is represented by the integral. -/
def fourierAtZero (h : ℝ → ℝ) : ℝ := ∫ z : ℝ, h z

def claim_12441 : Prop :=
  ∀ c : ℝ, 1 < c → ∀ h : ℝ → ℝ,
    h ∈ unsampledSources c →
      h 0 = 0 ∧ fourierAtZero h = 0 ∧ h ∈ exactS0

/-- The exact space of unsampled sources has arbitrarily large linearly
independent finite families. -/
def claim_12442 : Prop :=
  ∀ c : ℝ, 1 < c → InfiniteDimensionalSet (unsampledSources c)

def compactArithmeticImage (c : ℝ) (h : ℝ → ℝ) (x : ℝ) : ℝ :=
  (Real.rpow c (-1 / 2)) * Real.exp (x / 2) *
    Finset.sum (Finset.Icc (1 : ℕ) ⌊c * Real.exp (-x)⌋₊)
      (fun n => h ((n : ℝ) * Real.exp x / c))

/-- The compact arithmetic image vanishes on the complete compact cell. -/
def claim_12444 : Prop :=
  ∀ c : ℝ, 1 < c → ∀ h : ℝ → ℝ,
    h ∈ unsampledSources c →
      ∀ x : ℝ, 0 ≤ x → x ≤ Real.log c → compactArithmeticImage c h x = 0

end

end MathlibPlus.Open.ResearchFormalization.Unsampled
