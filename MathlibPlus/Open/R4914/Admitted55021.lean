import Mathlib

namespace MathlibPlus.Open.R4914

universe u

section FourierLines

variable {K : Type*} [Field K]
variable {V : Type u} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- Three one-dimensional summands with unique coordinates in their direct sum. -/
def directThreeLines (U : Fin 3 → Submodule K V) : Prop :=
  (∀ i, Module.finrank K (U i) = 1) ∧
    ∀ x : V, ∃! y : ∀ i, U i, ∑ i, (y i : V) = x

/-- The Fourier block coordinate used by the code in Claim 55021. -/
def fourierBlock (ζ : K) (U : Fin 3 → Submodule K V)
    (i : Fin 3) (x : ∀ k, U k) : V :=
  ∑ k, (ζ ^ (i.1 * k.1)) • (x k : V)

def fourierCode (ζ : K) (U : Fin 3 → Submodule K V) : Set (Fin 3 → V) :=
  Set.range (fun x : ∀ k, U k => fun i => fourierBlock ζ U i x)

def codeBlockProjection (ζ : K) (U : Fin 3 → Submodule K V) (i : Fin 3) :
    fourierCode ζ U → V :=
  fun y => y.1 i

/-- Claim 55021: with the retained order-three root of unity premise, the three
Fourier-code block projections are isomorphisms. -/
def fourierCodeProjection_55021
    (p : ℕ) [Fact (Nat.Prime p)]
    (V : Type u) [AddCommGroup V] [Module (ZMod p) V]
    [FiniteDimensional (ZMod p) V]
    (ζ : ZMod p) (U : Fin 3 → Submodule (ZMod p) V) : Prop :=
  7 ≤ p → orderOf ζ = 3 → directThreeLines U →
    ∀ i : Fin 3, ∃ e : (∀ k, U k) ≃ₗ[ZMod p] V,
      ∀ x, e x = fourierBlock ζ U i x

end FourierLines

end MathlibPlus.Open.R4914
