import Mathlib
import MathlibPlus.Open.Analysis.NormalizedProlateLeakage14987

open MeasureTheory Set
open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.Claim14975

noncomputable section

abbrev SourceFunction := ℝ → ℂ
abbrev FourierHilbert := MathlibPlus.Open.Analysis.EscapingProlate14987.FourierHilbert

/-- The unitary Fourier integral on the real source carrier. -/
noncomputable def unitaryFourier (f : SourceFunction) (ξ : ℝ) : ℂ :=
  Fourier.fourierIntegral Real.fourierChar (volume : Measure ℝ) f ξ

/-- The exact-source carrier occurring in the packet: even, smooth, compactly
supported in the open source band, with both displayed zero constraints. -/
def exactSource (lambda : ℝ) (f : SourceFunction) : Prop :=
  Function.Even f ∧
    (∀ x : ℝ, (f x).im = 0) ∧
      ContDiff ℝ (⊤ : WithTop ℕ∞) f ∧
        HasCompactSupport f ∧
          Function.support f ⊆ Ioo (-lambda) lambda ∧
            f 0 = 0 ∧
              unitaryFourier f 0 = 0 ∧
                MemLp f 2 (volume : Measure ℝ)

noncomputable def sourceToHilbert (f : SourceFunction)
    (hf : MemLp f 2 (volume : Measure ℝ)) : FourierHilbert :=
  MemLp.toLp f hf

noncomputable def leakageOf (lambda : ℝ) (f : SourceFunction)
    (hf : MemLp f 2 (volume : Measure ℝ)) : FourierHilbert :=
  MathlibPlus.Open.Analysis.EscapingProlate14987.finiteFourierLeakage lambda
    (sourceToHilbert f hf)

/-- The leakage image of a source subspace, using the actual complex L2 carrier. -/
def leakageImage (lambda : ℝ) (S : Submodule ℝ SourceFunction) : Set FourierHilbert :=
  {g | ∃ f : SourceFunction, f ∈ (S : Set SourceFunction) ∧
      ∃ hf : MemLp f 2 (volume : Measure ℝ), g = leakageOf lambda f hf}

/-- The leakage image of the full exact-source carrier. -/
def exactLeakageImage (lambda : ℝ) : Set FourierHilbert :=
  {g | ∃ f : SourceFunction, exactSource lambda f ∧
      ∃ hf : MemLp f 2 (volume : Measure ℝ), g = leakageOf lambda f hf}

/-- L2 orthogonality to a carrier set, with the complex inner product. -/
def l2OrthogonalTo (X : Set FourierHilbert) (g : FourierHilbert) : Prop :=
  ∀ h ∈ X, @inner ℂ FourierHilbert _ h g = 0

/-- Claim 14975: the normalized leakage complement is the orthogonal
complement of `T_lambda S` intersected with the exact-source leakage image. -/
def claim14975 (lambda : ℝ) (S : Submodule ℝ SourceFunction)
    (g : FourierHilbert) : Prop :=
  0 < lambda ∧
    Module.Finite ℝ S ∧
      (∀ f : S, exactSource lambda (f : SourceFunction)) ∧
        ‖g‖ = 1 ∧
          g ∈ exactLeakageImage lambda ∧
            l2OrthogonalTo (leakageImage lambda S) g

end
end MathlibPlus.Open.ResearchFormalization.Claim14975
