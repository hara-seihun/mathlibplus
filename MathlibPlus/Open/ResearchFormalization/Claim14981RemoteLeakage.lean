import Mathlib
import MathlibPlus.Open.Analysis.NormalizedProlateLeakage14987

open MeasureTheory Set Filter FourierTransform
open scoped BigOperators Topology

namespace MathlibPlus.Open.ResearchFormalization.Claim14981

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

def modulatedBump (eta : SourceFunction) (omega : ℝ) : SourceFunction :=
  fun x => eta x * (Real.cos (omega * x) : ℂ)

def modulationCombination {m : ℕ} (eta : SourceFunction)
    (omega : ℕ → Fin m → ℝ) (a : ℕ → Fin m → ℝ) : ℕ → SourceFunction :=
  fun n x => ∑ j : Fin m, (a n j : ℂ) * modulatedBump eta (omega n j) x

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

def remoteCarrierFamily {m : ℕ} (omega : ℕ → Fin m → ℝ) : Prop :=
  (∀ j : Fin m, Tendsto (fun n : ℕ => |omega n j|) atTop atTop) ∧
    (∀ j k : Fin m,
      Tendsto (fun n : ℕ => |omega n j + omega n k|) atTop atTop) ∧
      (∀ j k : Fin m, j ≠ k →
        Tendsto (fun n : ℕ => |omega n j - omega n k|) atTop atTop)

def exactFamily {m : ℕ} (lambda : ℝ)
    (S : Submodule ℝ SourceFunction)
    (hsS : ∀ s : S, MemLp (s : SourceFunction) 2 (volume : Measure ℝ))
    (eta : SourceFunction) (omega : ℕ → Fin m → ℝ)
    (a : ℕ → Fin m → ℝ) (f : ℕ → SourceFunction)
    (hf : ∀ n : ℕ, MemLp (f n) 2 (volume : Measure ℝ)) : Prop :=
  ∀ n : ℕ,
    f n = modulationCombination eta omega a n ∧
      sourceCore lambda (f n) ∧
        ‖sourceToHilbert (f n) (hf n)‖ = 1 ∧
          (∀ s : S,
            @inner ℂ FourierHilbert _
              (leakageOf lambda (s : SourceFunction) (hsS s))
              (leakageOf lambda (f n) (hf n)) = 0)

/-- Claim 14981: for the same exact source/modulation family, remote carriers
make the band-projected full Fourier transform vanish and make the exterior
leakage converge to that full unitary Fourier transform in L2. -/
def claim14981 : Prop :=
  ∀ (lambda : ℝ) (S : Submodule ℝ SourceFunction)
    (hsS : ∀ s : S, MemLp (s : SourceFunction) 2 (volume : Measure ℝ))
    (m : ℕ) (x₀ delta : ℝ) (eta : SourceFunction)
    (omega : ℕ → Fin m → ℝ) (a : ℕ → Fin m → ℝ)
    (f : ℕ → SourceFunction)
    (hf : ∀ n : ℕ, MemLp (f n) 2 (volume : Measure ℝ)),
    0 < lambda →
      0 < m →
        Module.Finite ℝ S →
          (∀ s : S, sourceCore lambda (s : SourceFunction)) →
            bumpMember lambda x₀ delta eta →
              remoteCarrierFamily omega →
                (∀ n : ℕ, ∀ j : Fin m,
                  0 < omega n j ∧ lambda < omega n j) →
                  exactFamily lambda S hsS eta omega a f hf →
                    Tendsto
                        (fun n : ℕ =>
                          ‖MathlibPlus.Open.Analysis.EscapingProlate14987.sourceProjection
                              lambda
                              (𝓕 (sourceToHilbert (f n) (hf n)))‖)
                        atTop (𝓝 0) ∧
                      Tendsto
                        (fun n : ℕ =>
                          ‖leakageOf lambda (f n) (hf n) -
                            𝓕 (sourceToHilbert (f n) (hf n))‖)
                        atTop (𝓝 0)

end
end MathlibPlus.Open.ResearchFormalization.Claim14981
