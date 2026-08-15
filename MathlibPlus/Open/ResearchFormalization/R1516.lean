import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R1516

noncomputable section

def skewRowMap {A B : Type*} (σ : Equiv.Perm A)
    (q : A → Equiv.Perm B) : A × B → A × B :=
  fun (a, b) => (σ a, q a b)

def permutationCentralizes {A : Type*} [Group A] (α : A ≃* A)
    (σ : Equiv.Perm A) : Prop :=
  ∀ a, α (σ a) = σ (α a)

def baseCentralizerMap {A B : Type*}
    (α : A → A) : A × B → A × B :=
  fun (a, b) => (α a, b)

def baseCentralizerAutomorphismProperty {A B : Type*} [Group A] [Group B]
    (α : A ≃* A) : Prop :=
  Function.Bijective (baseCentralizerMap (A := A) (B := B) α) ∧
    (∀ x y : A × B,
      baseCentralizerMap (A := A) (B := B) α (x * y) =
        baseCentralizerMap (A := A) (B := B) α x *
          baseCentralizerMap (A := A) (B := B) α y)

/-- The skew-row presentation and the induced base automorphism from a centralizer element. -/
def skewRowMapAndBaseCentralizer
    {A B : Type*} [Fintype A] [Fintype B] [Group A] [Group B]
    (σ : Equiv.Perm A) (q : A → Equiv.Perm B) (α : A ≃* A) : Prop :=
  (∀ a b, skewRowMap σ q (a, b) = (σ a, q a b)) ∧
    (permutationCentralizes α σ →
      baseCentralizerAutomorphismProperty (A := A) (B := B) α ∧
        ∀ (a : A) (b : B),
          baseCentralizerMap (A := A) (B := B) α (a, b) = (α a, b))

end

end MathlibPlus.Open.ResearchFormalization.R1516
