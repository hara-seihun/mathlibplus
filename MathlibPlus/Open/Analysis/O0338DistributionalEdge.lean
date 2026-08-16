import Mathlib

open scoped Distributions Topology
open Set TopologicalSpace Distribution

namespace MathlibPlus.Open.Analysis.O0338

noncomputable section

abbrev RealTestFunction := 𝓓((⊤ : TopologicalSpace.Opens ℝ), ℝ)
abbrev RealDistribution := 𝓓'((⊤ : TopologicalSpace.Opens ℝ), ℝ)

/-- A compact-support distributional pairing of a complex-valued function.
The test functions agree with the tested function on an open neighborhood of
`dsupport T`; the last clause records independence of that choice under the
same neighborhood condition. -/
def DistributionalPairing (T : RealDistribution) (g : ℝ → ℂ) (w : ℂ) : Prop :=
  ∃ U : Set ℝ, IsOpen U ∧ dsupport T ⊆ U ∧
    ∃ φre φim : RealTestFunction,
      (∀ x : ℝ, x ∈ U →
        φre x = (g x).re ∧ φim x = (g x).im) ∧
        w = ((T φre : ℝ) : ℂ) + Complex.I * ((T φim : ℝ) : ℂ) ∧
          ∀ V : Set ℝ, ∀ ψre ψim : RealTestFunction,
            IsOpen V → dsupport T ⊆ V →
              (∀ x : ℝ, x ∈ V →
                ψre x = (g x).re ∧ ψim x = (g x).im) →
                w = ((T ψre : ℝ) : ℂ) + Complex.I * ((T ψim : ℝ) : ℂ)

/-- The edge Cauchy transform defined by the canonical compact-support
pairing. -/
def CauchyTransform (T : RealDistribution) (C : ℂ → ℂ) : Prop :=
  ∀ z : ℂ, 0 < z.re →
    DistributionalPairing T
      (fun t : ℝ => (z + (t : ℂ))⁻¹) (C z)

/-- The branch of `log ζ` on the right half-plane used by the shifted
exponent. The real-axis normalization fixes the canonical branch. -/
def ZetaLogBranch (logZeta : ℂ → ℂ) : Prop :=
  AnalyticOnNhd ℂ logZeta {w : ℂ | 1 < w.re} ∧
    (∀ w : ℂ, 1 < w.re →
      Complex.exp (logZeta w) = riemannZeta w) ∧
      (∀ x : ℝ, 1 < x → (logZeta (x : ℂ)).im = 0)

/-- The shifted logarithm and its exponential, with all distributional values
realized by compactly supported test functions near the actual support. -/
def IsShiftedZetaExponent (T : RealDistribution) (a : ℝ)
    (logZeta L E : ℂ → ℂ) : Prop :=
  ZetaLogBranch logZeta ∧
    (∀ s : ℂ, 1 - a < s.re →
      DistributionalPairing T
        (fun α : ℝ => logZeta (s + (α : ℂ))) (L s)) ∧
      (∀ s : ℂ, 1 - a < s.re → E s = Complex.exp (L s))

/-- An edge cutoff is one on an open neighborhood of the portion of the
actual distributional support being retained, and is compactly supported near
that edge. -/
def IsAdmissibleEdgeCutoff (T : RealDistribution) (a δ : ℝ)
    (χ : RealTestFunction) : Prop :=
  ∃ U : Set ℝ,
    IsOpen U ∧ dsupport T ∩ Icc a (a + δ) ⊆ U ∧
      (∀ x : ℝ, x ∈ U → χ x = 1) ∧
        Function.support (χ : ℝ → ℝ) ⊆ Ioo (a - δ) (a + 2 * δ)

/-- Application of a translated edge cutoff to a test function. Equality is
required on an open neighborhood of the full distributional support, so
positive-order distributions see the intended jets and not an arbitrary
pointwise extension. -/
def EdgeCutoffApplication (T τ : RealDistribution) (a : ℝ)
    (χ : RealTestFunction) : Prop :=
  ∀ φ : RealTestFunction, ∃ ψ : RealTestFunction, ∃ V : Set ℝ,
    IsOpen V ∧ dsupport T ⊆ V ∧
      (∀ x : ℝ, x ∈ V → ψ x = χ x * φ (x - a)) ∧
        τ φ = T ψ

/-- A translated edge distribution, with cutoff independence whenever two
cutoffs agree on an open neighborhood of the actual distributional support. -/
def IsTranslatedEdgeCutoff (T τ : RealDistribution) (a δ : ℝ) : Prop :=
  ∃ χ : RealTestFunction,
    IsAdmissibleEdgeCutoff T a δ χ ∧
      EdgeCutoffApplication T τ a χ ∧
        ∀ χ' : RealTestFunction,
          (∃ V : Set ℝ, IsOpen V ∧ dsupport T ⊆ V ∧
            ∀ x : ℝ, x ∈ V → χ' x = χ x) →
              EdgeCutoffApplication T τ a χ'

/-- Claim 15518: a meromorphic continuation of the edge Cauchy transform
forces finite point support in every sufficiently small edge neighborhood. -/
def claim15518_meromorphic_cauchy_transform_local_finite_support : Prop :=
  ∀ (τ : RealDistribution) (R : ℝ),
    IsCompact (dsupport τ) → dsupport τ ⊆ Icc 0 R →
      ∀ C : ℂ → ℂ, CauchyTransform τ C →
        (∃ r : ℝ, 0 < r ∧
          ∃ F : ℂ → ℂ,
            MeromorphicOn F (Metric.ball (0 : ℂ) r) ∧
              (∀ z : ℂ, z ∈ Metric.ball (0 : ℂ) r → 0 < z.re →
                F z = C z)) →
          ∃ ε : ℝ, 0 < ε ∧
            ∀ η : ℝ, 0 < η → η < ε →
              Set.Finite (dsupport τ ∩ Ico 0 η)

/-- Claim 15520: after translating the least support point to zero and
cutting off the edge, the shifted-zeta logarithmic derivative is the edge
Cauchy transform plus a holomorphic remainder. -/
def claim15520_shifted_zeta_log_derivative_edge_cauchy_reduction : Prop :=
  ∀ (T : RealDistribution) (a : ℝ),
    T ≠ 0 → IsCompact (dsupport T) → IsLeast (dsupport T) a →
      ∃ logZeta L E : ℂ → ℂ,
        IsShiftedZetaExponent T a logZeta L E ∧
          ∃ r : ℝ, 0 < r ∧
            ∃ h : ℂ → ℂ,
              AnalyticOnNhd ℂ h (Metric.ball (0 : ℂ) r) ∧
                (∀ u : ℂ, u ∈ Metric.ball (0 : ℂ) r → u ≠ 0 →
                  -deriv riemannZeta (1 + u) / riemannZeta (1 + u) =
                    u⁻¹ + h u) ∧
                ∃ δ : ℝ, 0 < δ ∧
                  ∃ τ : RealDistribution, ∃ C H : ℂ → ℂ,
                    IsTranslatedEdgeCutoff T τ a δ ∧
                      CauchyTransform τ C ∧
                        AnalyticOnNhd ℂ H (Metric.ball (0 : ℂ) r) ∧
                          (∀ z : ℂ, z ∈ Metric.ball (0 : ℂ) r →
                            0 < z.re →
                              -deriv E (1 - (a : ℂ) + z) /
                                  E (1 - (a : ℂ) + z) = C z + H z)

/-- A nonzero meromorphic germ has a meromorphic logarithmic derivative; at
any pole its order is one and its residue is the signed integer order of the
original germ. -/
def claim15521_logDerivativeSimplePoles : Prop :=
  ∀ (f : ℂ → ℂ) (z₀ : ℂ),
    MeromorphicAt f z₀ → meromorphicOrderAt f z₀ ≠ ⊤ →
      MeromorphicAt (fun z => -logDeriv f z) z₀ ∧
        (meromorphicOrderAt (fun z => -logDeriv f z) z₀ < 0 →
          meromorphicOrderAt (fun z => -logDeriv f z) z₀ = (-1 : ℤ) ∧
            ∃ n : ℤ,
              meromorphicOrderAt f z₀ = n ∧
                meromorphicTrailingCoeffAt
                    (fun z => -logDeriv f z) z₀ = (-n : ℂ))

end

end MathlibPlus.Open.Analysis.O0338
