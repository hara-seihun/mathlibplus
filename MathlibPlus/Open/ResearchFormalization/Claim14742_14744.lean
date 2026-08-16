import MathlibPlus.Open.ResearchFormalization.Claim14739

open scoped BigOperators Matrix

namespace MathlibPlus.Open.ResearchFormalization.Claim14742_14744

noncomputable section

open MathlibPlus.Open.ResearchFormalization.Claim14739

/-- The two-component class-first function used in the rank-one kernel. -/
abbrev ChannelVector := ℝ → Fin 2 → ℂ

/-- The rank-one kernel `K(τ,w) = F(τ) F(w)ᵀ`, on its actual channel indices. -/
def rankOneKernel (F : ChannelVector) : ℝ → ℝ → Matrix (Fin 2) (Fin 2) ℂ :=
  fun τ w i j => F τ i * F w j

/--
Separate-variable linear processing of the two factors, followed by the
fixed channel/Reynolds/heat/recovery contraction.  The fixed contractions are
represented by their aggregate channel matrix `B`; the two linear maps act on
the two separate one-variable channel functions.
-/
def processedTwoChannel
    (F : ChannelVector)
    (P Q : ChannelVector →ₗ[ℂ] ChannelVector)
    (B : Matrix (Fin 2) (Fin 2) ℂ) : ℝ → ℝ → ℂ :=
  fun U Φ =>
    ∑ i : Fin 2, ∑ j : Fin 2,
      (P F) U i * B i j * (Q F) Φ j

/--
A two-component class-first rank-one source remains of arbitrary
split/compact separation rank at most two after arbitrary separate-variable
linear processing and fixed channel/Reynolds/heat/recovery contractions, and
therefore cannot equal either finite-heat target row at nonzero coupling.
-/
def claim14742 : Prop :=
  ∀ (F : ChannelVector)
    (P Q : ChannelVector →ₗ[ℂ] ChannelVector)
    (B : Matrix (Fin 2) (Fin 2) ℂ),
    let S := processedTwoChannel F P Q B
    separationRank S ≤ 2 ∧
      ∀ (x lam g : ℝ),
        0 < 2 + x →
        ∀ σ : ℝ, (σ = 1 ∨ σ = -1) → lam * g ≠ 0 →
          S ≠ finiteHeatRow x lam g σ

/--
For positive `d = 2 + x`, full Reynolds gives the exact split/compact
heat-rank drop: with `g ≠ 0` the rank is three for every nonzero `λ` and two
at `λ = 0`; with `g = 0` it is two for every `λ`.
-/
def claim14744 : Prop :=
  ∀ (x g : ℝ),
    0 < 2 + x →
      (g ≠ 0 →
        (∀ lam : ℝ, lam ≠ 0 →
          ∀ σ : ℝ, (σ = 1 ∨ σ = -1) →
            separationRank (finiteHeatRow x lam g σ) = 3) ∧
        (∀ σ : ℝ, (σ = 1 ∨ σ = -1) →
          separationRank (finiteHeatRow x 0 g σ) = 2)) ∧
      (g = 0 →
        ∀ lam : ℝ, ∀ σ : ℝ, (σ = 1 ∨ σ = -1) →
          separationRank (finiteHeatRow x lam 0 σ) = 2)

end

end MathlibPlus.Open.ResearchFormalization.Claim14742_14744
