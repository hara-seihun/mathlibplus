import Mathlib

namespace MathlibPlus.Open.ResearchChebyshev

open scoped Topology
open Filter

/-- The roots of the degree-`n` Chebyshev polynomial, indexed by `Fin n`.
This is the standard cosine parametrization of those roots. -/
noncomputable def chebyshevNode (n : ℕ) (k : Fin n) : ℝ :=
  Real.cos (((2 : ℝ) * (k : ℝ) + 1) * Real.pi / ((2 : ℝ) * (n : ℝ)))

/-- A polynomial of degree at most `n - 1` interpolating `f` at all roots of `T_n`. -/
def IsChebyshevInterpolant (f : ℝ → ℝ) (n : ℕ) (p : Polynomial ℝ) : Prop :=
  0 < n ∧
    p.natDegree < n ∧
      ∀ k : Fin n, p.eval (chebyshevNode n k) = f (chebyshevNode n k)

/-- Finite real subsequential limits of the Chebyshev interpolants at `x₀`.
The interpolating polynomial at each positive order is represented by its
characterizing property, so this definition does not add a choice of carrier. -/
def finiteChebyshevClusterSet (x₀ : ℝ) (f : ℝ → ℝ) : Set ℝ :=
  { y | ∃ ns : ℕ → ℕ,
      StrictMono ns ∧
        ∃ ps : ℕ → Polynomial ℝ,
          (∀ m, IsChebyshevInterpolant f (ns m) (ps m)) ∧
            Tendsto (fun m => (ps m).eval x₀) atTop (𝓝 y) }

/-- The interpolation and cluster-set specification underlying the notation. -/
def claim16197 : Prop :=
  (∀ (f : ℝ → ℝ) (n : ℕ),
    0 < n →
      ∃! p : Polynomial ℝ, IsChebyshevInterpolant f n p) ∧
    (∀ (x₀ : ℝ) (f : ℝ → ℝ) (y : ℝ),
      y ∈ finiteChebyshevClusterSet x₀ f ↔
        ∃ ns : ℕ → ℕ,
          StrictMono ns ∧
            ∃ ps : ℕ → Polynomial ℝ,
              (∀ m, IsChebyshevInterpolant f (ns m) (ps m)) ∧
                Tendsto (fun m => (ps m).eval x₀) atTop (𝓝 y))

/-- Every nonempty closed real target is a cluster set at every fixed point. -/
def claim16198 : Prop :=
  ∀ (x₀ : ℝ) (A : Set ℝ),
    x₀ ∈ Set.Icc (-1) 1 →
      A.Nonempty →
        IsClosed A →
          ∃ f : ℝ → ℝ,
            ContinuousOn f (Set.Icc (-1) 1) ∧
              finiteChebyshevClusterSet x₀ f = A

/-- Every nonempty closed subset of `[-1,1]` is a cluster set at every fixed point. -/
def claim16199 : Prop :=
  ∀ (x₀ : ℝ) (A : Set ℝ),
    x₀ ∈ Set.Icc (-1) 1 →
      A.Nonempty →
        A ⊆ Set.Icc (-1) 1 →
          IsClosed A →
            ∃ f : ℝ → ℝ,
              ContinuousOn f (Set.Icc (-1) 1) ∧
                finiteChebyshevClusterSet x₀ f = A

/-- A reduced rational ratio with odd positive denominator. -/
def HasOddReducedRationalDenominator (θ : ℝ) : Prop :=
  ∃ p : ℤ, ∃ q : ℕ,
    0 < q ∧
      Odd q ∧
        Nat.Coprime p.natAbs q ∧
          θ / Real.pi = (p : ℝ) / (q : ℝ)

/-- Exact classification of points admitting an empty finite cluster set. -/
def claim16200 : Prop :=
  ∀ θ₀ : ℝ,
    (∃ f : ℝ → ℝ,
      ContinuousOn f (Set.Icc (-1) 1) ∧
        finiteChebyshevClusterSet (Real.cos θ₀) f = ∅) ↔
      HasOddReducedRationalDenominator θ₀

/-- At an odd-rational angle there is a continuous function whose interpolants
have absolute values tending to infinity, and hence no finite cluster point. -/
def claim16201 : Prop :=
  ∀ θ₀ : ℝ,
    HasOddReducedRationalDenominator θ₀ →
      ∃ f : ℝ → ℝ,
        ContinuousOn f (Set.Icc (-1) 1) ∧
          (∃ ps : ℕ → Polynomial ℝ,
            (∀ n, IsChebyshevInterpolant f (n + 1) (ps n)) ∧
              Tendsto (fun n => |(ps n).eval (Real.cos θ₀)|) atTop atTop) ∧
          finiteChebyshevClusterSet (Real.cos θ₀) f = ∅

/-- Historical odd-positive-rational points realize every closed real target,
including the empty target. -/
def claim16202 : Prop :=
  ∀ (p q : ℕ),
    0 < p →
      0 < q →
        Odd p →
          Odd q →
            ∀ A : Set ℝ,
              IsClosed A →
                ∃ f : ℝ → ℝ,
                  ContinuousOn f (Set.Icc (-1) 1) ∧
                    finiteChebyshevClusterSet
                        (Real.cos (Real.pi * (p : ℝ) / (q : ℝ))) f = A

/-- The universal empty-target assertion fails away from odd-rational angles. -/
def claim16203 : Prop :=
  (∀ θ₀ : ℝ,
    ¬ HasOddReducedRationalDenominator θ₀ →
      ∀ f : ℝ → ℝ,
        ContinuousOn f (Set.Icc (-1) 1) →
          finiteChebyshevClusterSet (Real.cos θ₀) f ≠ ∅) ∧
    ¬ (∀ x₀ : ℝ,
      x₀ ∈ Set.Icc (-1) 1 →
        ∃ f : ℝ → ℝ,
          ContinuousOn f (Set.Icc (-1) 1) ∧
            finiteChebyshevClusterSet x₀ f = ∅)

end MathlibPlus.Open.ResearchChebyshev
