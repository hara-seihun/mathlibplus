import Mathlib

namespace MathlibPlus.Open.Analysis

open scoped BigOperators Topology

noncomputable section

/-- The Lambert weight appearing in the admitted block criterion. -/
def lambertWeight (j : ℕ) : ℝ :=
  sInf {w : ℝ | 0 ≤ w ∧ (j : ℝ) / (2 * Real.pi) ≤ w * Real.exp w}

/-- The residual gauge for a positive coefficient sequence. -/
def lambertResidual (a : ℕ → ℝ) (j : ℕ) : ℝ :=
  Real.log (8 * Real.pi * a j) + lambertWeight j

/-- The target-relative adjacent Lambert defect. -/
def adjacentLambertDefect (a : ℕ → ℝ) (j : ℕ) : ℝ :=
  Real.log (a j / a (j + 1)) - (lambertWeight (j + 1) - lambertWeight j)

/-- The supremum of a real-valued function over a finite index block. -/
def blockSup (I : ℕ → Finset ℕ) (f : ℕ → ℝ) (N : ℕ) : ℝ :=
  sSup (f '' ((I N : Finset ℕ) : Set ℕ))

/-- The cumulative defect used by the deterministic block criterion. -/
def cumulativeBlockDefect (a : ℕ → ℝ) (J₁ : ℕ → ℕ) (I : ℕ → Finset ℕ) (N : ℕ) : ℝ :=
  blockSup I
    (fun j => abs (Finset.sum (Finset.Ico j (J₁ N))
      (fun ℓ => adjacentLambertDefect a ℓ))) N

/--
The exact deterministic block criterion: small weighted endpoint residual plus
cumulative defect forces additive coefficient convergence, with the endpoint
weight variant under uniform Lambert-weight comparability.
-/
def deterministicBlockCriterion : Prop :=
  ∀ (a : ℕ → ℝ) (J₀ J₁ : ℕ → ℕ),
    (∀ j, 0 < a j) →
    (∀ N, 0 < J₀ N ∧ J₀ N ≤ J₁ N) →
    Filter.Tendsto (fun N => J₀ N) Filter.atTop Filter.atTop →
    Filter.Tendsto (fun N => J₁ N) Filter.atTop Filter.atTop →
    let I : ℕ → Finset ℕ := fun N => Finset.Icc (J₀ N) (J₁ N)
    let Ω : ℕ → ℝ := fun N => cumulativeBlockDefect a J₁ I N
    let endpointResidual : ℕ → ℝ :=
      fun N => |lambertResidual a (J₁ N)| + Ω N
    let additiveError : ℕ → ℝ :=
      fun N => blockSup I (fun j => |4 * (j : ℝ) * a j - lambertWeight j|) N
    let weightedEndpointError : ℕ → ℝ :=
      fun N => lambertWeight (J₁ N) * endpointResidual N
    let uniformWeightRatioError : ℕ → ℝ :=
      fun N => blockSup I
        (fun j => |lambertWeight j / lambertWeight (J₁ N) - 1|) N
    (Filter.Tendsto
        (fun N => blockSup I
          (fun j => lambertWeight j * endpointResidual N) N)
        Filter.atTop (𝓝 0) →
      Filter.Tendsto additiveError Filter.atTop (𝓝 0)) ∧
    (Filter.Tendsto uniformWeightRatioError Filter.atTop (𝓝 0) →
      Filter.Tendsto weightedEndpointError Filter.atTop (𝓝 0) →
        Filter.Tendsto additiveError Filter.atTop (𝓝 0))

end
end MathlibPlus.Open.Analysis
