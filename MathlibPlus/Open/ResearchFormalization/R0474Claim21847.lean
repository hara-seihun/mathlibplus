import MathlibPlus.Open.Research.R0474PoissonLaguerre21845

namespace MathlibPlus.Open.ResearchFormalization.R0474

noncomputable section

open scoped ENNReal lp Topology
open MathlibPlus.Open.Research.R0474PoissonLaguerre21845

/-- The genuine two-coordinate Hilbert fibre, using the Euclidean norm and
inner product on each Laguerre pair. -/
abbrev FeatureHilbert21847 :=
  lp (fun _ : ℕ => EuclideanSpace ℂ (Fin 2)) (2 : ℝ≥0∞)

/-- The reviewed Poisson--Laguerre pair embedded in the Euclidean two-coordinate
fibre of the sequence Hilbert space. -/
def featureCoordinate21847
    (x : ℝ) (z : ℂ) (n : ℕ) : EuclideanSpace ℂ (Fin 2) :=
  (EuclideanSpace.equiv (Fin 2) ℂ).symm
    ![(poissonLaguerreFirstShiftFeature x z n).1,
      (poissonLaguerreFirstShiftFeature x z n).2]

/-- Claim 21847: for every fixed positive parameter, the reviewed feature has
an actual map into the concrete sequence Hilbert carrier and that map is
complex differentiable at every complex point. -/
def claim21847_entireHilbertValuedFeatureMap : Prop :=
  ∀ x : ℝ, 0 < x →
    ∃ Φ : ℂ → FeatureHilbert21847,
      (∀ z : ℂ, ∀ n : ℕ,
        (Φ z) n = featureCoordinate21847 x z n) ∧
        Differentiable ℂ Φ

end

end MathlibPlus.Open.ResearchFormalization.R0474
