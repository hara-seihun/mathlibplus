import MathlibPlus.Open.ResearchFormalize.ConditionalNormalizationPathObstruction55455

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.R4922

noncomputable section

/-- A scale-one same-path repair is tested against the actual oriented-path
incidence and endpoint boundary, not defined by its desired coordinate values. -/
def samePathScaleOneRepair55454 {V : Type*} [DecidableEq V]
    {ℓ : ℕ} (P : Fin (ℓ + 1) → V)
    (q r : Fin ℓ → ℝ) : Prop :=
  (∀ i : Fin ℓ, 0 ≤ r i) ∧
    MathlibPlus.Open.ResearchFormalize.realPathIncidence P
        (fun i => q i + r i) =
      MathlibPlus.Open.ResearchFormalize.realPathEndpointBoundary P

def complementRepair55454 {s ℓ : ℕ}
    (Q : Fin s → Fin ℓ → ℝ) (j₀ : Fin s) : Fin ℓ → ℝ :=
  fun i => 1 - Q j₀ i

def decompositionNonnegative55454 {s ℓ : ℕ}
    (Q : Fin s → Fin ℓ → ℝ) : Prop :=
  ∀ (j : Fin s) (i : Fin ℓ), 0 ≤ Q j i

def unitCoordinateDecomposition55454 {s ℓ : ℕ}
    (Q : Fin s → Fin ℓ → ℝ) : Prop :=
  ∀ i : Fin ℓ, ∑ j : Fin s, Q j i = 1

/-- Claim 55454: on a nonempty finite simple path, the actual incidence
condition forces the unique scale-one repair to be the coordinate complement,
which is exactly the sum of the other decomposition components. -/
def coordinatewiseComplementRepair_claim55454 : Prop :=
  ∀ {V : Type*} [DecidableEq V] (ℓ : ℕ),
    0 < ℓ →
    ∀ (P : Fin (ℓ + 1) → V), Function.Injective P →
    ∀ (s : ℕ), 0 < s →
    ∀ (Q : Fin s → Fin ℓ → ℝ),
      decompositionNonnegative55454 Q →
      unitCoordinateDecomposition55454 Q →
      ∀ (j₀ : Fin s),
        samePathScaleOneRepair55454 P (Q j₀)
          (complementRepair55454 Q j₀) ∧
        (∀ (r : Fin ℓ → ℝ),
          samePathScaleOneRepair55454 P (Q j₀) r →
            (∀ i : Fin ℓ,
              r i = complementRepair55454 Q j₀ i) ∧
            (∀ i : Fin ℓ, Q j₀ i + r i = 1) ∧
            (∀ i : Fin ℓ,
              r i = ∑ j : Fin s,
                if j ≠ j₀ then Q j i else 0))

end

end MathlibPlus.Open.ResearchFormalization.R4922
