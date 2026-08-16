import Mathlib
import MathlibPlus.Open.Research.FormalizationBatchGammaJump

open MeasureTheory Set Filter Topology
open scoped BigOperators

namespace MathlibPlus.Open.Research.FormalizationBatch.O0191Fiber

noncomputable section

/-- The finite-cutoff Hilbert carrier `H_R = L²((-R,R))`. -/
abbrev H_R (R : ℝ) : Type :=
  MeasureTheory.Lp ℝ 2 (volume.restrict (Ioo (-R) R))

noncomputable def cutoffRestriction (R : ℝ) :
    MeasureTheory.Lp ℝ 2 (volume : Measure ℝ) →L[ℝ] H_R R :=
  MeasureTheory.LpToLpRestrictCLM ℝ ℝ ℝ (volume : Measure ℝ) 2
    (Ioo (-R) R)

noncomputable def cutoffExtension (R : ℝ) : H_R R →L[ℝ]
    MeasureTheory.Lp ℝ 2 (volume : Measure ℝ) :=
  (cutoffRestriction R).adjoint

noncomputable def unitaryTranslation (ell : ℝ) :
    MeasureTheory.Lp ℝ 2 (volume : Measure ℝ) →ₗᵢ[ℝ]
      MeasureTheory.Lp ℝ 2 (volume : Measure ℝ) :=
  MeasureTheory.Lp.compMeasurePreservingₗᵢ ℝ (fun x : ℝ => x + ell)
    (MeasureTheory.measurePreserving_add_right (volume : Measure ℝ) ell)

noncomputable def compressedTranslation (R ell : ℝ) : H_R R →L[ℝ] H_R R :=
  (cutoffRestriction R).comp
    ((unitaryTranslation ell).toContinuousLinearMap.comp (cutoffExtension R))

def cutoffInner {R : ℝ} (f g : H_R R) : ℝ :=
  inner ℝ f g

noncomputable def primeWeight (n : ℕ) : ℝ :=
  MathlibPlus.Open.Research.FormalizationBatchGammaJump.primeJumpCoefficient n

noncomputable def primeFiberAtShift (R ell : ℝ) (n : ℕ) (f : H_R R) : H_R R × H_R R :=
  (Real.sqrt (primeWeight n) • f,
    Real.sqrt (primeWeight n) • compressedTranslation R ell f)

noncomputable def primeFiberPair (R : ℝ) (n : ℕ) (f : H_R R) : H_R R × H_R R :=
  primeFiberAtShift R (Real.log (n : ℝ)) n f

noncomputable def offDiagonalPairing {R : ℝ}
    (u v u' v' : H_R R) : ℝ :=
  -cutoffInner u v' - cutoffInner v u'

/-- Essential compact support on the cutoff carrier, independent of the chosen
Lp representative. -/
def compactlySupported (R : ℝ) (f : H_R R) : Prop :=
  ∃ K : Set ℝ, IsCompact K ∧
    (∀ᵐ x ∂(volume.restrict (Ioo (-R) R)),
      x ∉ K → (f : ℝ → ℝ) x = 0)

def supportDiameterBound (R : ℝ) (f : H_R R) (d : ℝ) : Prop :=
  ∃ K : Set ℝ, IsCompact K ∧ Metric.diam K ≤ d ∧
    (∀ᵐ x ∂(volume.restrict (Ioo (-R) R)),
      x ∉ K → (f : ℝ → ℝ) x = 0)

/-- The finite Hilbert direct sum of the prime fibers through cutoff `X`. -/
abbrev PrimeFiberHilbert (R : ℝ) :=
  lp (fun _ : ℕ => H_R R × H_R R) 2

noncomputable def finitePrimeFiberMajorant (R : ℝ) (Y X : ℕ)
    (f : H_R R) : PrimeFiberHilbert R :=
  ∑ n ∈ Finset.Icc (max 2 Y) X,
    lp.single 2 n (primeFiberPair R n f)

/-- A norm on the exact prime-fiber direct sum that dominates its Hilbert norm. -/
def IsHilbertMajorantNorm {R : ℝ} (N : PrimeFiberHilbert R → ℝ) : Prop :=
  N 0 = 0 ∧
    (∀ z : PrimeFiberHilbert R, 0 ≤ N z) ∧
    (∀ z : PrimeFiberHilbert R, ‖z‖ ≤ N z) ∧
    (∀ c : ℝ, ∀ z : PrimeFiberHilbert R,
      N (c • z) = |c| * N z) ∧
    (∀ z w : PrimeFiberHilbert R,
      N (z + w) ≤ N z + N w)

/-- Claim 14949: the exact off-diagonal prime-fiber identity, its neutral
long-shift tail, and divergence for every Hilbert-majorant norm. -/
def claim_14949 : Prop :=
  ∀ R : ℝ, 0 < R → ∀ f : H_R R,
    compactlySupported R f → f ≠ 0 →
      (∀ n : ℕ, 2 ≤ n →
        offDiagonalPairing
            (primeFiberPair R n f).1 (primeFiberPair R n f).2
            (primeFiberPair R n f).1 (primeFiberPair R n f).2 =
          -2 * primeWeight n *
            cutoffInner f (compressedTranslation R (Real.log (n : ℝ)) f)) ∧
      (∃ d : ℝ, supportDiameterBound R f d ∧
        ∀ ell : ℝ, d < ell →
          ∀ n : ℕ, 2 ≤ n →
            offDiagonalPairing
                (primeFiberAtShift R ell n f).1
                (primeFiberAtShift R ell n f).2
                (primeFiberAtShift R ell n f).1
                (primeFiberAtShift R ell n f).2 = 0) ∧
      (∀ N : PrimeFiberHilbert R → ℝ,
        IsHilbertMajorantNorm N → ∀ Y : ℕ,
          Tendsto
            (fun X : ℕ => N (finitePrimeFiberMajorant R Y X f))
            atTop atTop)

end

end MathlibPlus.Open.Research.FormalizationBatch.O0191Fiber
