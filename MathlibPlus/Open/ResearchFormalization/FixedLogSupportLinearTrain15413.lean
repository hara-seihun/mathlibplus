import Mathlib

open Filter
open scoped BigOperators Topology

namespace MathlibPlus.Open.ResearchFormalization.FixedLogSupportLinearTrain15413

noncomputable section

/-- The projective first-jet determinant for the shadow and the boundary field. -/
def projectiveDeterminant (S B : ℂ → ℂ) (z : ℂ) : ℂ :=
  S z * deriv B z - deriv S z * B z

/-- The crossing graph in the closure of a domain. -/
def crossingSet (D : Set ℂ) (S B : ℂ → ℂ) : Set ℂ :=
  {z | z ∈ closure D ∧ ‖B z‖ = ‖S z‖}

/-- The interior part of the crossing graph. -/
def interiorCrossingSet (D : Set ℂ) (S B : ℂ → ℂ) : Set ℂ :=
  crossingSet D S B ∩ D

/-- Boundary endpoints of the crossing graph. -/
def boundaryCrossingSet (D : Set ℂ) (S B : ℂ → ℂ) : Set ℂ :=
  crossingSet D S B ∩ frontier D

/-- The projective critical vertices of the interior crossing graph. -/
def criticalCrossingSet (D : Set ℂ) (S B : ℂ → ℂ) : Set ℂ :=
  {z | z ∈ interiorCrossingSet D S B ∧ projectiveDeterminant S B z = 0}

/-- The regular part of the interior crossing graph. -/
def regularCrossingSet (D : Set ℂ) (S B : ℂ → ℂ) : Set ℂ :=
  {z | z ∈ interiorCrossingSet D S B ∧ projectiveDeterminant S B z ≠ 0}

/-- The regular arclength, represented by one-dimensional Hausdorff measure. -/
noncomputable def regularCrossingLength (D : Set ℂ) (S B : ℂ → ℂ) : ℝ :=
  ENNReal.toReal
    (MeasureTheory.Measure.hausdorffMeasure (1 : ℝ)
      (regularCrossingSet D S B))

/-- The literal transform supplied by the exact shadow/boundary split. -/
def literalTransform (S B : ℂ → ℂ) : ℂ → ℂ := fun z => S z + B z

/-- The zero set in a domain. -/
def zeroSet (D : Set ℂ) (F : ℂ → ℂ) : Set ℂ :=
  {z | z ∈ D ∧ F z = 0}

/-- A finite set's canonical finite representative; the empty value is used
when finiteness has not been supplied. -/
noncomputable def finiteToFinset (s : Set ℂ) : Finset ℂ := by
  classical
  exact if h : s.Finite then h.toFinset else ∅

/-- The zero count in a domain, with analytic multiplicity. -/
noncomputable def zeroCount (D : Set ℂ) (F : ℂ → ℂ) : ℕ := by
  classical
  exact ∑ z ∈ finiteToFinset (zeroSet D F), analyticOrderNatAt F z

/-- The endpoint/critical-jet charge of the crossing graph. -/
noncomputable def boundaryCriticalCharge (D : Set ℂ) (S B : ℂ → ℂ) : ℝ := by
  classical
  exact
    ((finiteToFinset (boundaryCrossingSet D S B)).card : ℝ) / 2 +
      ∑ v ∈ finiteToFinset (criticalCrossingSet D S B),
        ((analyticOrderNatAt (projectiveDeterminant S B) v + 1 : ℕ) : ℝ)

/-- The regular relative logarithmic derivative. -/
def relativeLogDerivative (S B : ℂ → ℂ) (z : ℂ) : ℂ :=
  deriv B z / B z - deriv S z / S z

/-- Two positive scales are comparable at infinity, i.e. each bounds the
other by a fixed positive constant eventually. -/
def asymptoticallyComparable (f g : ℕ → ℝ) : Prop :=
  ∃ a b : ℝ, 0 < a ∧ 0 < b ∧
    ∀ᶠ L : ℕ in atTop, a * g L ≤ f L ∧ f L ≤ b * g L

/-- Linear zero growth, the meaning of an `Ω(L)` zero train. -/
def linearZeroGrowth (N : ℕ → ℕ) : Prop :=
  ∃ κ : ℝ, 0 < κ ∧ ∃ L₀ : ℕ,
    ∀ L : ℕ, L₀ ≤ L → κ * (L : ℝ) ≤ (N L : ℝ)

/-- Claim 15413: if the exact literal split has a crossing graph whose regular
length is comparable with the fixed logarithmic-support scale, its regular
relative logarithmic derivative is at least `c L / S_L`, and its
endpoint/critical-jet charge is `o(L)`, then the zeros of the literal
transform in the domain form a linear train. -/
def fixedLogSupportLinearTrain_claim15413 : Prop :=
  ∀ (D : ℕ → Set ℂ) (S B : ℕ → ℂ → ℂ) (supportScale : ℕ → ℝ) (c : ℝ),
    0 < c →
      (∀ᶠ L : ℕ in atTop, 0 < supportScale L) →
      (∀ L : ℕ,
        IsOpen (D L) ∧
          IsConnected (D L) ∧
          Bornology.IsBounded (D L) ∧
          (∀ z : ℂ, z ∈ D L → 0 < z.im) ∧
          AnalyticOnNhd ℂ (S L) (closure (D L)) ∧
          AnalyticOnNhd ℂ (B L) (closure (D L)) ∧
          (∀ z : ℂ, z ∈ closure (D L) →
            ¬ (S L z = 0 ∧ B L z = 0)) ∧
          Set.Finite (boundaryCrossingSet (D L) (S L) (B L)) ∧
          Set.Finite (criticalCrossingSet (D L) (S L) (B L)) ∧
          Set.Finite
            (zeroSet (D L) (literalTransform (S L) (B L)))) →
        asymptoticallyComparable
          (fun L : ℕ => regularCrossingLength (D L) (S L) (B L))
          supportScale →
        Tendsto
          (fun L : ℕ =>
            boundaryCriticalCharge (D L) (S L) (B L) / (L : ℝ))
          atTop (𝓝 0) →
        (∀ (L : ℕ) (z : ℂ),
          z ∈ regularCrossingSet (D L) (S L) (B L) →
            ‖relativeLogDerivative (S L) (B L) z‖ ≥
              c * (L : ℝ) / supportScale L) →
        linearZeroGrowth
          (fun L : ℕ =>
            zeroCount (D L) (literalTransform (S L) (B L)))

end

end MathlibPlus.Open.ResearchFormalization.FixedLogSupportLinearTrain15413
