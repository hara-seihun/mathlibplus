import Mathlib

noncomputable section
open scoped BigOperators

namespace MathlibPlus.Open.AdmittedBatch

namespace MarginClaims

def membershipSet {α : Type*} [DecidableEq α]
    (A : Fin 3 → Finset α) (u : α) : Finset (Fin 3) :=
  Finset.univ.filter (fun i => u ∈ A i)

def exactMembershipCount {α : Type*} [DecidableEq α]
    (U : Finset α) (A : Fin 3 → Finset α) (S : Finset (Fin 3)) : ℕ :=
  (U.filter (fun u => membershipSet A u = S)).card

def properSubset3 :=
  {T : Finset (Fin 3) // T.Nonempty ∧ T ≠ Finset.univ}

def properMarginCount {α : Type*} [DecidableEq α]
    (U : Finset α) (A : Fin 3 → Finset α) (T : Finset (Fin 3)) : ℕ :=
  (U.filter (fun u => ∀ i ∈ T, u ∈ A i)).card

def properMarginProfile {α : Type*} [DecidableEq α]
    (U : Finset α) (A : Fin 3 → Finset α) :
    ℕ × (properSubset3 → ℕ) :=
  (U.card, fun T => properMarginCount U A T.1)

end MarginClaims

namespace TransportClaims

def fibreLeft {G I F : Type*} (σ : G → I ≃ I)
    (l : ∀ g : G, ∀ i : I, F ≃ F) (g : G) : I × F → I × F :=
  fun x => (σ g x.1, l g x.1 x.2)

def fibreRight {G I F : Type*} (σ : G → I ≃ I)
    (r : ∀ g : G, ∀ i : I, F ≃ F) (g : G) : I × F → I × F :=
  fun x => (σ g x.1, r g x.1 x.2)

def fibreTransport {I F : Type*} (h : ∀ i : I, F ≃ F) : I × F → I × F :=
  fun x => (x.1, h x.1 x.2)

def fibreSynchronizationCriterion : Prop :=
  ∀ {G I F : Type*} (σ : G → I ≃ I)
    (l r : ∀ g : G, ∀ i : I, F ≃ F)
    (h : ∀ i : I, F ≃ F),
    ((∀ g : G, ∀ x : I × F,
        fibreTransport h (fibreLeft σ l g x) =
          fibreRight σ r g (fibreTransport h x)) ↔
      ∀ g : G, ∀ i : I,
        (h (σ g i)).toFun ∘ (l g i).toFun =
          (r g i).toFun ∘ (h i).toFun)

end TransportClaims

end MathlibPlus.Open.AdmittedBatch
