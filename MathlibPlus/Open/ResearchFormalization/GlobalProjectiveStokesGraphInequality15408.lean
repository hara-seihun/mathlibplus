import Mathlib

open MeasureTheory
open scoped BigOperators ComplexConjugate Topology

namespace MathlibPlus.Open.ResearchFormalization.GlobalProjectiveStokesGraphInequality15408

noncomputable section

noncomputable def finiteToFinset (s : Set ℂ) : Finset ℂ := by
  classical
  exact if h : s.Finite then h.toFinset else ∅

def projectiveDelta (S B : ℂ → ℂ) (z : ℂ) : ℂ :=
  S z * deriv B z - deriv S z * B z

def projectiveCrossingSet (D : Set ℂ) (S B : ℂ → ℂ) : Set ℂ :=
  {z : ℂ | z ∈ closure D ∧ ‖B z‖ = ‖S z‖}

noncomputable def domainZeroCount (D : Set ℂ) (F : ℂ → ℂ) : ℕ :=
  ∑ z ∈ finiteToFinset {w : ℂ | w ∈ D ∧ F w = 0},
    analyticOrderNatAt F z

noncomputable def projectivePhaseFlux
    (D : Set ℂ) (S B : ℂ → ℂ) (V : Finset ℂ) : ℝ :=
  (1 / (2 * Real.pi)) *
    ∫ z in projectiveCrossingSet D S B \ (V : Set ℂ),
      ‖projectiveDelta S B z / (S z * B z)‖
        ∂(Measure.hausdorffMeasure 1)

noncomputable def projectiveCriticalLoad
    (D : Set ℂ) (S B : ℂ → ℂ) (V : Finset ℂ) : ℝ :=
  ((Set.ncard
      (projectiveCrossingSet D S B ∩ frontier D) : ℕ) : ℝ) / 2 +
    ∑ v ∈ V,
      ((analyticOrderNatAt (projectiveDelta S B) v + 1 : ℕ) : ℝ)

/-- The number of incidences of parameterized open graph edges at a vertex;
a self-loop therefore contributes two half-edges. -/
def edgeHalfEdgeCount {m : ℕ}
    (edges : Fin m → ℝ → ℂ) (v : ℂ) : ℕ :=
  Finset.univ.sum (fun i : Fin m =>
    (if edges i 0 = v then 1 else 0) +
      (if edges i 1 = v then 1 else 0))

/-- Record 10's concrete carrier: a bounded Jordan domain, analytic shadow
and boundary fields, and a finite real-analytic crossing graph together with
its closed regular components, boundary transversality, and critical local
orders. -/
def projectiveStokesRecord10
    (D : Set ℂ) (S B : ℂ → ℂ) (boundary : ℝ → ℂ)
    (edgeCount loopCount : ℕ)
    (edges : Fin edgeCount → ℝ → ℂ)
    (loops : Fin loopCount → ℝ → ℂ)
    (V : Finset ℂ) : Prop :=
  IsOpen D ∧
    D.Nonempty ∧
    IsConnected D ∧
    Bornology.IsBounded D ∧
    AnalyticOnNhd ℂ S (closure D) ∧
    AnalyticOnNhd ℂ B (closure D) ∧
    (∀ z : ℂ, z ∈ closure D →
      ¬ (S z = 0 ∧ B z = 0)) ∧
    AnalyticOnNhd ℝ boundary Set.univ ∧
    Function.Periodic boundary 1 ∧
    Set.range boundary = frontier D ∧
    (∀ s t : ℝ,
      s ∈ Set.Icc (0 : ℝ) 1 →
        t ∈ Set.Icc (0 : ℝ) 1 →
          boundary s = boundary t →
            s = t ∨ (s = 0 ∧ t = 1) ∨ (s = 1 ∧ t = 0)) ∧
    (∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
      deriv boundary t ≠ 0) ∧
    let Γ := projectiveCrossingSet D S B
    let Δ := projectiveDelta S B
    (∀ z : ℂ, z ∈ Γ → S z ≠ 0 ∧ B z ≠ 0) ∧
      Set.Finite (Γ ∩ frontier D) ∧
      (∀ i : Fin edgeCount,
        AnalyticOnNhd ℝ (edges i) Set.univ ∧
          (∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
            deriv (edges i) t ≠ 0) ∧
          (∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
            edges i t ∈ closure D) ∧
          (∀ t : ℝ, t ∈ Set.Ioo (0 : ℝ) 1 →
            edges i t ∈ D ∧ Δ (edges i t) ≠ 0)) ∧
      (∀ j : Fin loopCount,
        AnalyticOnNhd ℝ (loops j) Set.univ ∧
          loops j 0 = loops j 1 ∧
          (∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
            deriv (loops j) t ≠ 0) ∧
          (∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
            loops j t ∈ D ∧ Δ (loops j t) ≠ 0)) ∧
      Γ =
        (⋃ i : Fin edgeCount,
          edges i '' Set.Icc (0 : ℝ) 1) ∪
          (⋃ j : Fin loopCount,
            loops j '' Set.Icc (0 : ℝ) 1) ∧
      (∀ z : ℂ, z ∈ (V : Set ℂ) ↔
        z ∈ Γ ∧ Δ z = 0) ∧
      Set.Finite (V : Set ℂ) ∧
      (∀ z : ℂ, z ∈ Γ → z ∈ frontier D →
        edgeHalfEdgeCount edges z = 1 ∧
          ∃ i : Fin edgeCount, ∃ t u : ℝ,
            t ∈ Set.Icc (0 : ℝ) 1 ∧
              u ∈ Set.Icc (0 : ℝ) 1 ∧
              edges i t = z ∧
              boundary u = z ∧
              Complex.im
                (conj (deriv (edges i) t) * deriv boundary u) ≠ 0) ∧
      (∀ v : ℂ, v ∈ (V : Set ℂ) →
        edgeHalfEdgeCount edges v =
          2 * (analyticOrderNatAt Δ v + 1))

/-- Claim 15408: the phase flux of the regular analytic crossing graph is
paid for by its literal zero count and the boundary/critical charge. -/
def globalProjectiveStokesGraphInequality_claim15408 : Prop :=
  ∀ (D : Set ℂ) (S B : ℂ → ℂ) (boundary : ℝ → ℂ)
    (edgeCount loopCount : ℕ)
    (edges : Fin edgeCount → ℝ → ℂ)
    (loops : Fin loopCount → ℝ → ℂ)
    (V : Finset ℂ),
    projectiveStokesRecord10
      D S B boundary edgeCount loopCount edges loops V →
      (domainZeroCount D (fun z => S z + B z) : ℝ) +
          projectiveCriticalLoad D S B V ≥
        projectivePhaseFlux D S B V

end

end MathlibPlus.Open.ResearchFormalization.GlobalProjectiveStokesGraphInequality15408
