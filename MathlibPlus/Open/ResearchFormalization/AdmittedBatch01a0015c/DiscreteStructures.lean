import Mathlib

namespace MathlibPlus.Open.ResearchFormalization

/-- Claim 14221: the two exact component-stabilizer predicates. -/
def claim14221 {V C : Type*} (R S : C → Set V)
    (σ ρ : Equiv.Perm V) : Prop :=
  (∀ component, σ '' R component = S component) ∧
    (∀ component, ρ '' R component = R component)

/-- Claim 14222: global pairings form a stabilizer coset. -/
def claim14222 {V C : Type*} (R S : C → Set V) : Prop :=
  ∀ (σ₀ : Equiv.Perm V),
    (∀ component, σ₀ '' R component = S component) →
      ∀ σ : Equiv.Perm V,
        (∀ component, σ '' R component = S component) ↔
          ∃ ρ : Equiv.Perm V,
            (∀ component, ρ '' R component = R component) ∧
              (∀ v : V, σ v = σ₀ (ρ v))

/-- Claim 14223: the pairing-count dichotomy and its trivial-stabilizer case. -/
def claim14223 {V C : Type*} (R S : C → Set V) : Prop :=
  let P := {σ : Equiv.Perm V // ∀ component, σ '' R component = S component}
  let Aut := {ρ : Equiv.Perm V // ∀ component, ρ '' R component = R component}
  Cardinal.mk P = 0 ∨
      (Cardinal.mk P = Cardinal.mk Aut ∧
        (Cardinal.mk P ≠ 0 →
          (Cardinal.mk P = 1 ↔
            ∀ ρ : Equiv.Perm V,
              (∀ component, ρ '' R component = R component) →
                ρ = Equiv.refl V)))

end MathlibPlus.Open.ResearchFormalization
