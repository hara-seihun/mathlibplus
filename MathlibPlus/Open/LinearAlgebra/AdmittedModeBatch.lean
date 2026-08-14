import Mathlib

namespace MathlibPlus.Open.LinearAlgebra

/-- The three-mode parameter space for submodules `U₀,U₁,U₂`. -/
abbrev modeParameterSpace {K V : Type*} [Ring K] [AddCommGroup V]
    [Module K V] (U : Fin 3 → Submodule K V) :=
  U 0 × (U 1 × U 2)

def modeValue {K V : Type*} [Ring K] [AddCommGroup V]
    [Module K V] (U : Fin 3 → Submodule K V) (ζ : K) (i : Fin 3)
    (u : modeParameterSpace U) : V :=
  (u.1 : V) + ζ ^ i.1 • (u.2.1 : V) + ζ ^ (2 * i.1) • (u.2.2 : V)

/-- A precise direct-sum formulation of the labelled mode shadow and of the
three coordinate isomorphisms. -/
def hasThreeModeDecomposition {K V : Type*} [Field K]
    [AddCommGroup V] [Module K V]
    (ζ : K) (P : Submodule K (Fin 3 → V)) : Prop :=
  ∃ U : Fin 3 → Submodule K V,
    (∀ v : V, ∃! u : modeParameterSpace U,
      (u.1 : V) + (u.2.1 : V) + (u.2.2 : V) = v) ∧
    (∀ i : Fin 3,
      ∃ e : modeParameterSpace U ≃ₗ[K] V,
        ∀ u, e u = modeValue U ζ i u) ∧
    (∀ x : Fin 3 → V, x ∈ P ↔
      ∃ u : modeParameterSpace U,
        ∀ i : Fin 3, x i = modeValue U ζ i u)

def cyclicModeIndex (i : Fin 3) : Fin 3 :=
  ⟨(i.1 + 1) % 3, by omega⟩

def cyclicBlockShift {V : Type*} (x : Fin 3 → V) : Fin 3 → V :=
  fun i => x (cyclicModeIndex i)

def cyclicShiftInvariant {K V : Type*} [Ring K]
    [AddCommGroup V] [Module K V]
    (P : Submodule K (Fin 3 → V)) : Prop :=
  ∀ x, x ∈ P → cyclicBlockShift x ∈ P

def coordinateProjectionsAreIsomorphisms {K V : Type*} [Field K]
    [AddCommGroup V] [Module K V]
    (P : Submodule K (Fin 3 → V)) : Prop :=
  ∀ i : Fin 3,
    ∃ e : P ≃ₗ[K] V,
      ∀ x : P, e x = x.1 i

def distinctCubicRoots {K : Type*} [Field K] (ζ : K) : Prop :=
  ζ ^ 3 = 1 ∧ ζ ≠ 1 ∧ ζ ^ 2 ≠ 1 ∧
    (∀ z : K, z ^ 3 = 1 → z = 1 ∨ z = ζ ∨ z = ζ ^ 2)

/-- Claim 54916: over each elementary primary field in the stated rank range,
the cyclic code has the labelled semisimple three-mode form, and the second
code has its corresponding labelled form. -/
def semisimpleThreeModeDecomposition : Prop :=
  ∀ (p : ℕ), (hp : p.Prime) → p ≠ 3 →
    ∀ (r : ℕ), 1 ≤ r → r ≤ 3 →
      letI : Fact p.Prime := ⟨hp⟩
      let K := ZMod p
      let V := Fin r → K
      ∀ (ζ : K), distinctCubicRoots ζ →
        ∀ (P Q : Submodule K (Fin 3 → V)),
          cyclicShiftInvariant P →
          coordinateProjectionsAreIsomorphisms P →
          cyclicShiftInvariant Q →
          coordinateProjectionsAreIsomorphisms Q →
          hasThreeModeDecomposition ζ P ∧
          hasThreeModeDecomposition ζ Q

end MathlibPlus.Open.LinearAlgebra
