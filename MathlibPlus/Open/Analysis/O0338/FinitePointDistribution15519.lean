import MathlibPlus.Open.ResearchFormalization.O0338.Claim15522

open scoped BigOperators Distributions Topology
open Set TopologicalSpace Distribution

namespace MathlibPlus.Open.ResearchFormalization.O0338

open MathlibPlus.Open.Analysis.O0338

noncomputable section

/-- A compact distribution whose support is finite and lies in the reviewed
nonnegative edge interval. -/
def finitePointSupported15519 (T : RealDistribution) : Prop :=
  ∃ R : ℝ,
    IsCompact (Distribution.dsupport T) ∧
      Distribution.dsupport T ⊆ Set.Icc 0 R ∧
        Set.Finite (Distribution.dsupport T)

/-- A finite distributional jet expansion at points in the edge interval. -/
def finitePointJetExpansion15519
    (T : RealDistribution) (R : ℝ) (m r : ℕ)
    (t : Fin m → ℝ) (c : Fin m → Fin (r + 1) → ℝ) : Prop :=
  Distribution.dsupport T ⊆ Set.range t ∧
    (∀ j : Fin m, t j ∈ Set.Icc 0 R) ∧
      ∀ φ : 𝓓((⊤ : TopologicalSpace.Opens ℝ), ℝ),
        T φ =
          (∑ j : Fin m, ∑ k : Fin (r + 1),
            (c j k) • deltaDerivative (t j) k.1) φ

/-- The exact Cauchy pairing of one delta derivative on the reviewed
nonnegative support domain. -/
def deltaDerivativeCauchyPairing15519 : Prop :=
  ∀ (t : ℝ) (k : ℕ) (z : ℂ),
    0 ≤ t →
      0 < z.re →
        DistributionalPairing (deltaDerivative t k)
          (fun x : ℝ => (z + (x : ℂ))⁻¹)
          ((Nat.factorial k : ℂ) /
            (z + (t : ℂ)) ^ (k + 1))

/-- The Cauchy transform of a finite jet expansion is the corresponding finite
sum of factorial principal parts. -/
def finitePointCauchyExpansion15519 : Prop :=
  ∀ (T : RealDistribution) (R : ℝ) (m r : ℕ)
    (t : Fin m → ℝ) (c : Fin m → Fin (r + 1) → ℝ),
    finitePointJetExpansion15519 T R m r t c →
      ∀ C : ℂ → ℂ, CauchyTransform T C →
        ∀ z : ℂ, 0 < z.re →
          C z =
            ∑ j : Fin m, ∑ k : Fin (r + 1),
              (c j k : ℂ) * (Nat.factorial k.1 : ℂ) /
                (z + (t j : ℂ)) ^ (k.1 + 1)

/-- The pole order of the `k`-th delta derivative is exactly `k+1`; hence the
jet order is one less than the Cauchy pole order. -/
def deltaDerivativeCauchyPoleOrder15519 : Prop :=
  ∀ (t : ℝ) (k : ℕ),
    0 ≤ t →
      meromorphicOrderAt
          (fun z : ℂ =>
            (Nat.factorial k : ℂ) /
              (z + (t : ℂ)) ^ (k + 1))
          (-(t : ℂ)) = (-(k + 1 : ℤ) : WithTop ℤ)

/-- Claim 15519: compact distributions with finite point support are finite
sums of delta derivatives, with the exact factorial Cauchy principal parts and
pole-order/derivative-order correspondence. -/
def claim15519_finitePointDistributions : Prop :=
  (∀ T : RealDistribution,
    finitePointSupported15519 T →
      ∃ (R : ℝ) (m r : ℕ) (t : Fin m → ℝ)
        (c : Fin m → Fin (r + 1) → ℝ),
        finitePointJetExpansion15519 T R m r t c) ∧
    deltaDerivativeCauchyPairing15519 ∧
    finitePointCauchyExpansion15519 ∧
    deltaDerivativeCauchyPoleOrder15519

end

end MathlibPlus.Open.ResearchFormalization.O0338
