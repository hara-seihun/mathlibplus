import Mathlib
import MathlibPlus.Open.Analysis.NormalizedProlateLeakage14987

open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace MathlibPlus.Open.ResearchFormalization.Claim14979

noncomputable section

abbrev SourceFunction := ℝ → ℂ
abbrev FourierHilbert := MathlibPlus.Open.Analysis.EscapingProlate14987.FourierHilbert

noncomputable def unitaryFourier (f : SourceFunction) (xi : ℝ) : ℂ :=
  Fourier.fourierIntegral Real.fourierChar (volume : Measure ℝ) f xi

def sourceCore (lambda : ℝ) (f : SourceFunction) : Prop :=
  Function.Even f ∧
    (∀ x : ℝ, (f x).im = 0) ∧
      ContDiff ℝ (⊤ : WithTop ℕ∞) f ∧
        HasCompactSupport f ∧
          Function.support f ⊆ Ioo (-lambda) lambda ∧
            f 0 = 0 ∧ unitaryFourier f 0 = 0

noncomputable def sourceToHilbert (f : SourceFunction)
    (hf : MemLp f 2 (volume : Measure ℝ)) : FourierHilbert :=
  MemLp.toLp f hf

noncomputable def leakageOf (lambda : ℝ) (f : SourceFunction)
    (hf : MemLp f 2 (volume : Measure ℝ)) : FourierHilbert :=
  MathlibPlus.Open.Analysis.EscapingProlate14987.finiteFourierLeakage lambda
    (sourceToHilbert f hf)

noncomputable def sourceInner (f g : SourceFunction) : ℂ :=
  ∫ x : ℝ, star (f x) * g x

noncomputable def sourceEnergy (eta : SourceFunction) : ℝ :=
  ∫ x : ℝ, ‖eta x‖ ^ 2

/-- The nonzero even smooth bump, supported in two symmetric intervals away
from zero and inside the source band. -/
def bumpMember (lambda x₀ delta : ℝ) (eta : SourceFunction) : Prop :=
  (∃ x : ℝ, eta x ≠ 0) ∧
    Function.Even eta ∧
      (∀ x : ℝ, (eta x).im = 0) ∧
        ContDiff ℝ (⊤ : WithTop ℕ∞) eta ∧
          HasCompactSupport eta ∧
            0 < delta ∧
              delta < x₀ ∧
                x₀ + delta < lambda ∧
                  Function.support eta ⊆
                    (Ioo (-x₀ - delta) (-x₀ + delta) ∪
                      Ioo (x₀ - delta) (x₀ + delta))

def modulatedBump (eta : SourceFunction) (omega : ℝ) : SourceFunction :=
  fun x => eta x * (Real.cos (omega * x) : ℂ)

def carrierSeparation {m : ℕ} (omega : ℕ → Fin m → ℝ) : Prop :=
  (∀ j k : Fin m,
    Tendsto (fun n : ℕ => |omega n j + omega n k|) atTop atTop) ∧
    (∀ j k : Fin m, j ≠ k →
      Tendsto (fun n : ℕ => |omega n j - omega n k|) atTop atTop)

def modulationCombination {m : ℕ} (eta : SourceFunction)
    (omega : ℕ → Fin m → ℝ) (a : Fin m → ℝ) (n : ℕ) : SourceFunction :=
  fun x => ∑ j : Fin m, (a j : ℂ) * modulatedBump eta (omega n j) x

def euclideanUnit {m : ℕ} (a : Fin m → ℝ) : Prop :=
  ∑ j : Fin m, a j ^ 2 = 1

def leakageImage (lambda : ℝ) (S : Submodule ℝ SourceFunction) : Set FourierHilbert :=
  {g | ∃ f : SourceFunction, f ∈ (S : Set SourceFunction) ∧
      ∃ hf : MemLp f 2 (volume : Measure ℝ), g = leakageOf lambda f hf}

noncomputable def leakageSpan (lambda : ℝ) (S : Submodule ℝ SourceFunction) :
    Submodule ℝ FourierHilbert :=
  Submodule.span ℝ (leakageImage lambda S)

def exactConstraint (lambda : ℝ) (S : Submodule ℝ SourceFunction)
    (hsS : ∀ s : S, MemLp (s : SourceFunction) 2 (volume : Measure ℝ))
    (f : SourceFunction) (hf : MemLp f 2 (volume : Measure ℝ)) : Prop :=
  sourceCore lambda f ∧
    (∀ s : S,
      @inner ℂ FourierHilbert _
        (leakageOf lambda (s : SourceFunction) (hsS s))
        (leakageOf lambda f hf) = 0)

def normalizeSource (f : SourceFunction) (r : ℝ) : SourceFunction :=
  fun x => f x / (r : ℂ)

/-- Claim 14979: separated modulations have the diagonal Gram limit.  A
Euclidean-unit vector in the exact zero-Fourier/leakage-orthogonality kernel
has uniformly bounded nonzero L2 norm, and scalar normalization preserves all
of those exact constraints on the same `T_lambda S` carrier. -/
def claim14979 : Prop :=
  ∀ (lambda : ℝ) (S : Submodule ℝ SourceFunction)
    (hsS : ∀ s : S, MemLp (s : SourceFunction) 2 (volume : Measure ℝ))
    (m : ℕ) (x₀ delta : ℝ) (eta : SourceFunction)
    (omega : ℕ → Fin (m + 2) → ℝ),
    0 < lambda →
      Module.Finite ℝ S →
        (∀ s : S, sourceCore lambda (s : SourceFunction)) →
          m = Module.finrank ℝ (leakageSpan lambda S) →
              bumpMember lambda x₀ delta eta →
                carrierSeparation omega →
                  (∀ j k : Fin (m + 2),
                    Tendsto
                      (fun n : ℕ =>
                        sourceInner (modulatedBump eta (omega n j))
                          (modulatedBump eta (omega n k)))
                      atTop
                      (𝓝 (if j = k then (sourceEnergy eta / 2 : ℂ) else 0))) ∧
                    ∃ (lower upper : ℝ) (N : ℕ),
                      0 < lower ∧
                        0 < upper ∧
                          ∀ n : ℕ, N ≤ n →
                            ∀ a : Fin (m + 2) → ℝ,
                              euclideanUnit a →
                                ∀ hf : MemLp
                                  (modulationCombination eta omega a n)
                                  2 (volume : Measure ℝ),
                                  exactConstraint lambda S hsS
                                      (modulationCombination eta omega a n) hf →
                                    lower ≤
                                        ‖sourceToHilbert
                                          (modulationCombination eta omega a n) hf‖ ∧
                                      ‖sourceToHilbert
                                          (modulationCombination eta omega a n) hf‖ ≤ upper ∧
                                        ∃ hnorm : MemLp
                                          (normalizeSource
                                            (modulationCombination eta omega a n)
                                            ‖sourceToHilbert
                                              (modulationCombination eta omega a n) hf‖)
                                          2 (volume : Measure ℝ),
                                          exactConstraint lambda S hsS
                                            (normalizeSource
                                              (modulationCombination eta omega a n)
                                              ‖sourceToHilbert
                                                (modulationCombination eta omega a n) hf‖)
                                            hnorm

end
end MathlibPlus.Open.ResearchFormalization.Claim14979
