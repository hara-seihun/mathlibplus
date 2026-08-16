import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.BatchO0078

open scoped BigOperators

noncomputable section

noncomputable def complexLine (σ t : ℝ) : ℂ :=
  (σ : ℂ) - (t : ℂ) * Complex.I

noncomputable def gammaCarrier (m : ℕ) (s : ℂ) : ℂ :=
  Complex.exp (-(s / 2) * Complex.log (Real.pi : ℂ)) *
    Complex.Gamma ((m : ℂ) + s / 2)

noncomputable def xi (s : ℂ) : ℂ :=
  (s * (s - 1) / 2) *
    Complex.exp (-(s / 2) * Complex.log (Real.pi : ℂ)) *
    Complex.Gamma (s / 2) * riemannZeta s

noncomputable def xiLine (σ : ℝ) : ℝ → ℂ :=
  fun t => xi (complexLine σ t)

noncomputable def carrierRadius (m : ℕ) (σ t : ℝ) : ℝ :=
  ‖gammaCarrier m (complexLine σ t)‖

noncomputable def normalizedXi (m : ℕ) (σ t : ℝ) : ℂ :=
  xi (complexLine σ t) / (carrierRadius m σ t : ℂ)

noncomputable def trigamma (z : ℂ) : ℂ :=
  deriv Complex.digamma z

noncomputable def shiftedClock (m : ℕ) (σ t : ℝ) : ℝ :=
  (1 / 4 : ℝ) *
    (trigamma ((m : ℂ) + complexLine σ t / 2)).re

noncomputable def curvature (f : ℝ → ℂ) (t : ℝ) : ℝ :=
  ‖deriv f t‖ ^ 2 -
    (deriv (deriv f) t * starRingEnd ℂ (f t)).re

def claim12114 : Prop :=
  ∀ (m : ℕ) (σ t : ℝ),
    1 ≤ m →
    (1 / 2 : ℝ) ≤ σ →
    σ ≤ 1 →
    curvature (xiLine σ) t =
      carrierRadius m σ t ^ 2 *
        (curvature (fun x => normalizedXi m σ x) t +
          shiftedClock m σ t * ‖normalizedXi m σ t‖ ^ 2)

noncomputable def h6 (u : ℝ) : ℝ :=
  (1 / 12 : ℝ) *
    Finset.sum (Finset.Icc 1 (Nat.floor (Real.exp u))) (fun n =>
      ((n : ℝ) / Real.exp u) ^ 2 *
        (1 - ((n : ℝ) / Real.exp u) ^ 2) ^ 3 *
        (11 * ((n : ℝ) / Real.exp u) ^ 2 - 3))

noncomputable def H6 (s : ℂ) : ℂ :=
  32 * (s - 1) * riemannZeta s /
    ((s + 2) * (s + 4) * (s + 6) * (s + 8) * (s + 10))

noncomputable def nonnegativeVolume : MeasureTheory.Measure ℝ :=
  MeasureTheory.MeasureSpace.volume.restrict (Set.Ici (0 : ℝ))

noncomputable def H6Laplace (s : ℂ) : ℂ :=
  ∫ u, Complex.exp (-s * (u : ℂ)) * (h6 u : ℂ) ∂nonnegativeVolume

def claim12121 : Prop :=
  ∀ s : ℂ, H6 s = H6Laplace s

noncomputable def h6IntegerValue (N : ℕ) : ℝ :=
  (((N : ℝ) - 1) * ((N : ℝ) + 1) * (2 * (N : ℝ) - 5) *
      (2 * (N : ℝ) - 1) * (2 * (N : ℝ) + 1) * (2 * (N : ℝ) + 5)) /
    (360 * (N : ℝ) ^ 9)

noncomputable def h6AsymptoticError (θ : ℝ) (N : ℕ) : ℝ :=
  h6 (Real.log ((N : ℝ) + θ)) -
    ((2 : ℝ) / 45 - (4 / 3 : ℝ) * θ ^ 2 * (1 - θ) ^ 2) *
      ((N : ℝ) ^ 3)⁻¹

def h6BigOTheta (θ : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ‖h6AsymptoticError θ N‖ ≤ C * ((N : ℝ) ^ 4)⁻¹

def h6HasInfinitelyManySignChanges : Prop :=
  ∀ R : ℝ, ∃ x y : ℝ,
    0 < x ∧ x < y ∧ R < x ∧
      ((h6 (Real.log x) < 0 ∧ 0 < h6 (Real.log y)) ∨
        (0 < h6 (Real.log x) ∧ h6 (Real.log y) < 0))

def claim12122 : Prop :=
  (∀ N : ℕ, 1 ≤ N →
    h6 (Real.log (N : ℝ)) = h6IntegerValue N) ∧
  h6 (Real.log (2 : ℝ)) < 0 ∧
  (∀ N : ℕ, 3 ≤ N → 0 < h6 (Real.log (N : ℝ))) ∧
  (∀ θ : ℝ, 0 ≤ θ → θ < 1 → h6BigOTheta θ) ∧
  Set.Infinite {N : ℕ |
    h6 (Real.log ((N : ℝ) + (1 / 2 : ℝ))) < 0} ∧
  h6HasInfinitelyManySignChanges

noncomputable def gammaPhase (σ t : ℝ) : ℂ :=
  Complex.exp (Complex.I * Complex.arg (gammaCarrier 6 (complexLine σ t)))

noncomputable def q6 (σ t : ℝ) : ℝ :=
  (1 / 2 : ℝ) *
    (Real.log Real.pi -
      (Complex.digamma (6 + complexLine σ t / 2)).re)

noncomputable def moment (σ t : ℝ) (j : ℕ) : ℂ :=
  ∫ u,
    (((u + q6 σ t) ^ j : ℝ) : ℂ) *
      Complex.exp (-(σ : ℂ) * (u : ℂ)) *
      (h6 u : ℂ) *
      Complex.exp (Complex.I * ((t * u : ℝ) : ℂ)) ∂nonnegativeVolume

noncomputable def normalizedXiFromMoments (σ : ℝ) : ℝ → ℂ :=
  fun t => gammaPhase σ t * moment σ t 0

noncomputable def B6 (t p : ℝ) : ℝ :=
  ∫ u,
    h6 u * h6 (p - u) * Real.cos (t * (2 * u - p)) ∂
      (MeasureTheory.MeasureSpace.volume.restrict (Set.Icc (0 : ℝ) p))

noncomputable def doubleMomentKernel (σ t : ℝ) : ℝ :=
  ∫ u,
    (∫ v,
      (1 / 2 : ℝ) *
        Real.exp (-σ * (u + v)) * h6 u * h6 v *
        (u + v + 2 * q6 σ t) ^ 2 * Real.cos (t * (u - v))
      ∂nonnegativeVolume) ∂nonnegativeVolume

noncomputable def convolutionMomentKernel (σ t : ℝ) : ℝ :=
  (1 / 2 : ℝ) *
    ∫ p,
      Real.exp (-σ * p) * (p + 2 * q6 σ t) ^ 2 * B6 t p
      ∂nonnegativeVolume

def claim12126 : Prop :=
  ∀ (σ t : ℝ),
    curvature (normalizedXiFromMoments σ) t =
        ‖moment σ t 1‖ ^ 2 +
          (moment σ t 2 * starRingEnd ℂ (moment σ t 0)).re ∧
      curvature (normalizedXiFromMoments σ) t =
        doubleMomentKernel σ t ∧
      curvature (normalizedXiFromMoments σ) t =
        convolutionMomentKernel σ t

end

end MathlibPlus.Open.ResearchFormalization.BatchO0078
