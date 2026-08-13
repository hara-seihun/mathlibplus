import Mathlib

namespace MathlibPlus.Analysis

open scoped BigOperators

/-- Claim 8579: a finite positive ensemble has free-energy derivative equal to
minus its normalized expected energy.  The Gaussian hole ensemble is obtained
by taking the states to be the `m`-element hole sets, the base mass to be the
positive Vandermonde/dual-weight factor, and the energy to be the sum of the
logarithmic node coordinates. -/
theorem freeEnergy_firstDerivative_claim8579
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (baseMass energy : Ω → ℝ) (hbase : ∀ ω, 0 < baseMass ω)
    (t : ℝ) (_ht0 : 0 ≤ t) (_ht1 : t ≤ 1) :
    HasDerivAt
      (fun s : ℝ => Real.log (∑ ω : Ω,
        baseMass ω * Real.exp (-(s * energy ω))))
      (-(∑ ω : Ω,
          baseMass ω * (energy ω * Real.exp (-(t * energy ω)))) /
        (∑ ω : Ω, baseMass ω * Real.exp (-(t * energy ω)))) t := by
  have harg (ω : Ω) :
      HasDerivAt (fun s : ℝ => -(s * energy ω)) (-energy ω) t := by
    have h : HasDerivAt (fun s : ℝ => s * energy ω) (1 * energy ω) t :=
      (hasDerivAt_id t).mul_const (energy ω)
    have h' := h.neg
    change HasDerivAt (-(fun s : ℝ => s * energy ω)) (-energy ω) t
    simpa using h'
  have hexp (ω : Ω) :
      HasDerivAt (fun s : ℝ => Real.exp (-(s * energy ω)))
        (-(energy ω) * Real.exp (-(t * energy ω))) t := by
    have h := (Real.hasDerivAt_exp (-(t * energy ω))).comp t (harg ω)
    simpa [Function.comp_def, mul_comm, mul_left_comm, mul_assoc] using h
  have hterm (ω : Ω) :
      HasDerivAt (fun s : ℝ => baseMass ω * Real.exp (-(s * energy ω)))
        (baseMass ω * (-(energy ω) * Real.exp (-(t * energy ω)))) t := by
    exact HasDerivAt.const_mul (baseMass ω) (hexp ω)
  have hsum0 := (HasDerivAt.sum (u := (Finset.univ : Finset Ω))
      (fun ω _ => hterm ω))
  have hsum :
      HasDerivAt (fun s : ℝ => ∑ ω : Ω,
          baseMass ω * Real.exp (-(s * energy ω)))
        (∑ ω : Ω,
          baseMass ω * (-(energy ω) * Real.exp (-(t * energy ω)))) t := by
    have hfun :
        (∑ ω ∈ (Finset.univ : Finset Ω),
            (fun s : ℝ => baseMass ω * Real.exp (-(s * energy ω)))) =
          (fun s : ℝ => ∑ ω : Ω,
            baseMass ω * Real.exp (-(s * energy ω))) := by
      funext s
      simp
    exact hsum0.congr_of_eventuallyEq
      (Filter.Eventually.of_forall (fun s => by rw [hfun]))
  have hpos : 0 < (∑ ω : Ω,
      baseMass ω * Real.exp (-(t * energy ω))) := by
    apply Finset.sum_pos
    · intro ω hω
      exact mul_pos (hbase ω) (Real.exp_pos _)
    · exact Finset.univ_nonempty
  have hlog := hsum.log (ne_of_gt hpos)
  have hnum :
      (∑ ω : Ω,
          baseMass ω * (-(energy ω) * Real.exp (-(t * energy ω)))) =
        -(∑ ω : Ω,
          baseMass ω * (energy ω * Real.exp (-(t * energy ω)))) := by
    calc
      (∑ ω : Ω,
          baseMass ω * (-(energy ω) * Real.exp (-(t * energy ω)))) =
          ∑ ω : Ω, -(baseMass ω *
            (energy ω * Real.exp (-(t * energy ω)))) := by
            apply Finset.sum_congr rfl
            intro ω hω
            ring
      _ = -(∑ ω : Ω,
          baseMass ω * (energy ω * Real.exp (-(t * energy ω)))) := by
        rw [Finset.sum_neg_distrib]
  rw [hnum] at hlog
  exact hlog

end MathlibPlus.Analysis
