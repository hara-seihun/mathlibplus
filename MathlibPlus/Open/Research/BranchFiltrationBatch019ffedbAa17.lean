import Mathlib

namespace MathlibPlus.Open.Research.BranchFiltrationBatch019ffedbAa17

/-- The graded piece of a decreasing submodule filtration at degree `p`. -/
abbrev gradedPiece {V : Type*} [AddCommGroup V] [Module ℚ V]
    (F : ℕ → Submodule ℚ V) (p : ℕ) : Type _ :=
  F p ⧸ (F (p + 1)).comap (F p).subtype

/-- Claim 5237: a finite decreasing rational branch filtration has finite-dimensional graded pieces. -/
def finiteDecreasingBranchFiltration : Prop :=
  ∀ (V : Type*) [AddCommGroup V] [Module ℚ V]
    [FiniteDimensional ℚ V] (height : ℕ) (F : ℕ → Submodule ℚ V),
    (∀ p : ℕ, F (p + 1) ≤ F p) →
    F 0 = ⊤ →
    F (height + 1) = ⊥ →
    ∀ p : ℕ, FiniteDimensional ℚ (gradedPiece F p)

/-- The class of a filtered vector in the degree-`p` associated graded quotient. -/
def gradedClass {V : Type*} [AddCommGroup V] [Module ℚ V]
    (F : ℕ → Submodule ℚ V) (p : ℕ) (x : F p) : gradedPiece F p :=
  Submodule.Quotient.mk x

/-- Membership formulations of preservation and one-step filtration raising. -/
def preservesFiltration {V W : Type*} [AddCommGroup V] [Module ℚ V]
    [AddCommGroup W] [Module ℚ W]
    (F : ℕ → Submodule ℚ V) (G : ℕ → Submodule ℚ W)
    (f : V →ₗ[ℚ] W) : Prop :=
  ∀ p : ℕ, ∀ x : F p, f (x : V) ∈ G p

def raisesFiltration {V W : Type*} [AddCommGroup V] [Module ℚ V]
    [AddCommGroup W] [Module ℚ W]
    (F : ℕ → Submodule ℚ V) (G : ℕ → Submodule ℚ W)
    (f : V →ₗ[ℚ] W) : Prop :=
  ∀ p : ℕ, ∀ x : F p, f (x : V) ∈ G (p + 1)

/-- Claim 5239: a filtration-raising map vanishes on the same-degree associated graded,
while adding it to a filtration-preserving map leaves that graded map unchanged. -/
def associatedGradedRaisingMapsVanish : Prop :=
  ∀ (V W : Type*) [AddCommGroup V] [Module ℚ V]
    [AddCommGroup W] [Module ℚ W]
    (F : ℕ → Submodule ℚ V) (G : ℕ → Submodule ℚ W)
    (hdec : ∀ p : ℕ, G (p + 1) ≤ G p)
    (d₀ d₁ : V →ₗ[ℚ] W)
    (h₀ : preservesFiltration F G d₀)
    (h₁ : raisesFiltration F G d₁),
    (∀ p : ℕ, ∀ x : F p,
      gradedClass G p ⟨(d₀ + d₁) (x : V),
        add_mem (h₀ p x) (hdec p (h₁ p x))⟩ =
      gradedClass G p ⟨d₀ (x : V), h₀ p x⟩) ∧
    (∀ p : ℕ, ∀ x : F p,
      gradedClass G p ⟨d₁ (x : V), hdec p (h₁ p x)⟩ = 0)

end MathlibPlus.Open.Research.BranchFiltrationBatch019ffedbAa17
