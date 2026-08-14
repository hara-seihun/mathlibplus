import Mathlib

namespace MathlibPlus.Open.FiniteCayleyCI

abbrev V := Fin 2 → ZMod 3

def IdentityFree (S : Set V) : Prop :=
  (0 : V) ∉ S

def InverseClosed (S : Set V) : Prop :=
  ∀ ⦃x : V⦄, x ∈ S → -x ∈ S

def cayleyGraph (S : Set V) (h₀ : IdentityFree S)
    (hInv : InverseClosed S) : SimpleGraph V where
  Adj v w := w - v ∈ S
  symm := by
    constructor
    intro v w h
    have hneg : -(w - v) ∈ S := hInv h
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hneg
  loopless := by
    constructor
    intro v h
    exact h₀ (by simpa using h)

noncomputable def cayleyValency (S : Set V) (h₀ : IdentityFree S)
    (hInv : InverseClosed S) (v : V) : ℕ :=
  Set.ncard {w : V | (cayleyGraph S h₀ hInv).Adj v w}

def linearImageClaim : Prop :=
  ∀ (S T : Set V),
    IdentityFree S → InverseClosed S →
    IdentityFree T → InverseClosed T →
    Set.ncard S = Set.ncard T →
    ∃ A : V ≃ₗ[ZMod 3] V, A '' S = T

def cayleyCIConsequence : Prop :=
  ∀ (S T : Set V)
    (hS₀ : IdentityFree S) (hSInv : InverseClosed S)
    (hT₀ : IdentityFree T) (hTInv : InverseClosed T),
    let Gₛ := cayleyGraph S hS₀ hSInv
    let Gₜ := cayleyGraph T hT₀ hTInv
    ∀ (_e : Gₛ ≃g Gₜ),
      (∀ v : V,
        cayleyValency S hS₀ hSInv v =
          cayleyValency T hT₀ hTInv (_e v)) ∧
      Set.ncard S = Set.ncard T ∧
      ∃ A : V ≃ₗ[ZMod 3] V, A '' S = T

end MathlibPlus.Open.FiniteCayleyCI
