import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.NewResearch2.R0079

noncomputable section

/-- Claim 17753: the two-channel entire datum with the prescribed affine
imaginary shift. -/
def claim17753_twoChannelEntireDatum
    (a c d : ℂ → ℂ)
    (E : ℝ → ℂ → Fin 2 → ℂ) : Prop :=
  Differentiable ℂ a ∧ Differentiable ℂ c ∧ Differentiable ℂ d ∧
    ∀ x : ℝ, ∀ z : ℂ,
      E x z 0 = a z + Complex.I * (x : ℂ) ∧
        E x z 1 = c z + Complex.I * d z

/-- Claim 17754: the two-channel de Branges kernel is exactly the kernel of
its affine finite pencil. -/
def claim17754_twoChannelDeBrangesKernelFormula
    (N : ℕ)
    (a c d : ℂ → ℂ)
    (E : ℝ → ℂ → Fin 2 → ℂ)
    (kernel : ℝ → ℂ → ℂ → ℂ)
    (A B : Matrix (Fin N) (Fin N) ℝ)
    (feature : ℂ → Fin N → ℂ) : Prop :=
  let Esharp : ℝ → ℂ → Fin 2 → ℂ := fun x z i ↦
    starRingEnd ℂ (E x (starRingEnd ℂ z) i)
  let pencilKernel : ℝ → ℂ → ℂ → ℂ := fun x z w ↦
    ∑ i : Fin N, ∑ j : Fin N,
      starRingEnd ℂ (feature z i) *
        ((A i j : ℂ) + (x : ℂ) * (B i j : ℂ)) * feature w j
  (Differentiable ℂ a ∧ Differentiable ℂ c ∧ Differentiable ℂ d) ∧
    (∀ x : ℝ, ∀ z : ℂ,
      E x z 0 = a z + Complex.I * (x : ℂ) ∧
        E x z 1 = c z + Complex.I * d z) ∧
    ∀ x : ℝ, ∀ z w : ℂ, z ≠ w →
      kernel x z w =
          ((∑ i : Fin 2, E x z i * Esharp x w i) -
            (∑ i : Fin 2, Esharp x z i * E x w i)) /
            (2 * Complex.I * (z - w)) ∧
        kernel x z w = pencilKernel x z w

/-- Claim 17755: the finite negative-square index is the negative inertia of
the Hermitian affine pencil. -/
def claim17755_finiteNegativeSquareIndexIsInertia
    (A B : ∀ N : ℕ, Matrix (Fin N) (Fin N) ℝ)
    (kappa : ℕ → ℝ → ℕ) : Prop :=
  let negativeIndex : ∀ N : ℕ, Matrix (Fin N) (Fin N) ℝ → ℕ := fun N K ↦
    let negativeSubspace : ℕ → Prop := fun d ↦
      ∃ U : Submodule ℝ (Fin N → ℝ),
        Module.finrank ℝ U = d ∧
          ∀ v : Fin N → ℝ, v ∈ U → v ≠ 0 →
            ∑ i : Fin N, ∑ j : Fin N, v i * K i j * v j < 0
    letI : DecidablePred negativeSubspace :=
      fun d ↦ Classical.propDecidable (negativeSubspace d)
    Nat.findGreatest negativeSubspace N
  (∀ N : ℕ, ∀ i j : Fin N,
      A N i j = A N j i ∧ B N i j = B N j i) ∧
    ∀ N : ℕ, ∀ x : ℝ,
      kappa N x = negativeIndex N (A N + x • B N)

/-- Claim 17756: the spectrahedral, Schur-Hamiltonian, and de Branges index
charts define the same real parameter set. -/
def claim17756_threeEquivalentPositivityIndexCharts
    (A B : ∀ N : ℕ, Matrix (Fin N) (Fin N) ℝ)
    (schurHamiltonian : ℕ → ℝ → ℝ)
    (kappa : ℕ → ℝ → ℕ) : Prop :=
  let positiveDefinite : ∀ N : ℕ, Matrix (Fin N) (Fin N) ℝ → Prop :=
    fun N M ↦
      ∀ v : Fin N → ℝ, v ≠ 0 →
        0 < ∑ i : Fin N, ∑ j : Fin N, v i * M i j * v j
  let admissible : Set ℝ :=
    {x : ℝ | ∀ N : ℕ, positiveDefinite N (A N + x • B N)}
  let schurChart : Set ℝ :=
    {x : ℝ | ∀ m : ℕ, 0 < schurHamiltonian m x}
  let indexChart : Set ℝ :=
    {x : ℝ | ∀ N : ℕ, kappa N x = 0}
  (admissible = schurChart ∧ schurChart = indexChart) ∧
    (∀ N : ℕ, ∀ i j : Fin N,
      A N i j = A N j i ∧ B N i j = B N j i)

/-- Claim 17758: the exact Poisson modularity law and its even fixed point. -/
def claim17758_exactPoissonModularity
    (S : ℝ → ℝ → ℝ) : Prop :=
  (∀ x u : ℝ,
    S x (-u) = S (2 - x) u + 2 * (x - 1) * Real.cosh (u / 2)) ∧
    (∀ u : ℝ, S 1 (-u) = S 1 u)

end

end MathlibPlus.Open.NewResearch2.R0079
