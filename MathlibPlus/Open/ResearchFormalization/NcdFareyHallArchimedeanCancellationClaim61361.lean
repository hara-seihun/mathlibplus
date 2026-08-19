import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.NcdFareyHallArchimedeanCancellationClaim61361

noncomputable section

/-- The standard completed-zeta function used by the admitted claim. -/
def standardCompletion (s : ℂ) : ℂ :=
  (Real.pi : ℂ) ^ (-s / 2) * Complex.Gamma (s / 2) * riemannZeta s

/-- The regular locus on which both displayed completions have finite
meromorphic factors.  The Gamma nonvanishing conditions avoid Mathlib's
 totalized values at Gamma poles. -/
def displayedFactorsFinite (s : ℂ) : Prop :=
  s ≠ 0 ∧
    s ≠ 1 ∧
      s + 1 ≠ 0 ∧
        s + 1 ≠ 1 ∧
          Complex.Gamma (s / 2) ≠ 0 ∧
            Complex.Gamma ((s + 1) / 2) ≠ 0

/-- The finite Euler factor of the Farey-row ratio. -/
def fareyRowFiniteEulerFactor (s : ℂ) : ℂ :=
  riemannZeta (s + 1) / riemannZeta s

/-- The finite Euler factor occurring in the completed-zeta Hall ratio. -/
def completedHallFiniteEulerFactor (s : ℂ) : ℂ :=
  riemannZeta s / riemannZeta (s + 1)

/-- The KSV scalar kernel under the convention that `ζ*` is the standard
completion. -/
def ksvScalarKernel (s : ℂ) : ℂ :=
  standardCompletion s / standardCompletion (s + 1)

/-- The archimedean factor left after finite Euler cancellation. -/
def archimedeanGammaRatio (s : ℂ) : ℂ :=
  (Real.sqrt Real.pi : ℂ) *
    (Complex.Gamma (s / 2) / Complex.Gamma ((s + 1) / 2))

/-- Claim 61361: the standard-completion cancellation and its half-plane
Farey/Hall interpretation. -/
def claim61361 : Prop :=
  (∀ s : ℂ,
    displayedFactorsFinite s →
      riemannZeta s ≠ 0 →
        riemannZeta (s + 1) ≠ 0 →
          (riemannZeta (s + 1) / riemannZeta s) *
            (standardCompletion s / standardCompletion (s + 1)) =
          (Real.sqrt Real.pi : ℂ) *
            (Complex.Gamma (s / 2) /
              Complex.Gamma ((s + 1) / 2))) ∧
    (∀ s : ℂ, 1 < s.re →
      fareyRowFiniteEulerFactor s * completedHallFiniteEulerFactor s = 1 ∧
        fareyRowFiniteEulerFactor s * ksvScalarKernel s =
          archimedeanGammaRatio s)

end

end MathlibPlus.Open.ResearchFormalization.NcdFareyHallArchimedeanCancellationClaim61361
