import Mathlib

open MeasureTheory Set Filter FourierTransform Classical
open scoped BigOperators

namespace MathlibPlus.Open.Analysis.EscapingProlate14987

noncomputable section

/-- The `L²(ℝ)` carrier on which the unitary Fourier transform acts. -/
abbrev FourierHilbert := Lp ℂ 2 (volume : Measure ℝ)

/-- The exterior frequency region for `P_lambda`. -/
def exteriorRegion (lambda : ℝ) : Set ℝ :=
  {ξ : ℝ | lambda < |ξ|}

/-- Multiplication by `1_{[-lambda,lambda]}` on the actual `L²` carrier. -/
noncomputable def sourceProjection
    (lambda : ℝ) (f : FourierHilbert) : FourierHilbert :=
  MemLp.toLp (Set.indicator (Set.Icc (-lambda) lambda) (fun x => f x))
    (MemLp.indicator measurableSet_Icc (Lp.memLp f))

/-- Multiplication by the exterior indicator on the actual `L²` carrier. -/
noncomputable def exteriorProjection
    (lambda : ℝ) (f : FourierHilbert) : FourierHilbert :=
  MemLp.toLp (Set.indicator (exteriorRegion lambda) (fun x => f x))
    (MemLp.indicator
      (measurableSet_lt measurable_const measurable_abs) (Lp.memLp f))

/-- The exact exterior finite-Fourier leakage map
`T_lambda=(I-P_lambda) F P_lambda`. -/
def finiteFourierLeakage
    (lambda : ℝ) (f : FourierHilbert) : FourierHilbert :=
  exteriorProjection lambda (𝓕 (sourceProjection lambda f))

/-- The source-window condition for a zero-extended mode. -/
def sourceWindow (lambda : ℝ) (f : FourierHilbert) : Prop :=
  sourceProjection lambda f = f

/-- Evenness and real-valuedness of an even source mode. -/
def evenSourceMode (lambda : ℝ) (f : FourierHilbert) : Prop :=
  sourceWindow lambda f ∧
    (∀ᵐ x : ℝ ∂(volume : Measure ℝ), f (-x) = f x) ∧
    (∀ᵐ x : ℝ ∂(volume : Measure ℝ), (f x).im = 0)

/-- The squared norm `d_{nu,c}=||T_lambda p_{nu,c}||²`. -/
def leakageEnergy (lambda : ℝ) (f : FourierHilbert) : ℝ :=
  ‖finiteFourierLeakage lambda f‖ ^ 2

/-- The individually normalized exterior leakage
`q=d^(-1/2)(I-P_lambda) F P_lambda p`. -/
noncomputable def normalizedLeakage
    (lambda : ℝ) (f : FourierHilbert) : FourierHilbert :=
  (Real.sqrt (leakageEnergy lambda f))⁻¹ • finiteFourierLeakage lambda f

/-- The positive logarithmic coordinate, with its unitary Jacobian. -/
def positiveLogLeakageCoordinate
    (lambda : ℝ) (f : FourierHilbert) (y : ℝ) : ℝ :=
  if 0 < y then
    Real.sqrt (lambda * Real.exp y) *
      (normalizedLeakage lambda f (lambda * Real.exp y)).re
  else 0

/-- The normalized leakage is real and even on the exterior. -/
def realEvenExteriorLeakage
    (lambda : ℝ) (f : FourierHilbert) : Prop :=
  (∀ᵐ ξ : ℝ ∂(volume : Measure ℝ),
      ξ ∈ exteriorRegion lambda →
        (normalizedLeakage lambda f ξ).im = 0) ∧
    (∀ᵐ ξ : ℝ ∂(volume : Measure ℝ),
      ξ ∈ exteriorRegion lambda →
        (normalizedLeakage lambda f (-ξ)).re =
          (normalizedLeakage lambda f ξ).re)

/-- The exact singular-vector carrier used for the prolate modes.  The
Fourier leakage is the displayed finite map, the source modes are orthonormal,
and each mode is an eigenvector of the leakage Gram form. -/
def normalizedProlateModeFamily
    (lambda : ℝ) (p : ℕ → FourierHilbert) : Prop :=
  0 < lambda ∧
    (∀ nu : ℕ,
      evenSourceMode lambda (p nu) ∧
        0 < leakageEnergy lambda (p nu) ∧
        realEvenExteriorLeakage lambda (p nu) ∧
        (∀ g : FourierHilbert,
          inner ℂ (finiteFourierLeakage lambda (p nu))
              (finiteFourierLeakage lambda g) =
            (leakageEnergy lambda (p nu) : ℂ) * inner ℂ (p nu) g)) ∧
    (∀ nu mu : ℕ,
      inner ℂ (p nu) (p mu) = if nu = mu then 1 else 0)

/-- Claim 14987: for normalized positive logarithmic leakage coordinates of
these even prolate modes, the exact inner product is one half of the Kronecker
_delta. -/
def normalized_prolate_leakage_orthogonality_claim14987 : Prop :=
  ∀ lambda c : ℝ, 0 < lambda → c = lambda ^ 2 →
    ∀ (p : ℕ → FourierHilbert),
      normalizedProlateModeFamily lambda p →
        ∀ nu mu : ℕ,
          (∫ y in Set.Ioi (0 : ℝ),
            positiveLogLeakageCoordinate lambda (p nu) y *
              positiveLogLeakageCoordinate lambda (p mu) y) =
            if nu = mu then 1 / 2 else 0

end
end MathlibPlus.Open.Analysis.EscapingProlate14987
