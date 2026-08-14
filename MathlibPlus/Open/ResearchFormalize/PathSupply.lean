import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalize

/-- Directed incidence of the successive edges of an injectively indexed path. -/
def pathIncidence {V : Type*} [DecidableEq V] {ℓ : ℕ}
    (P : Fin (ℓ + 1) → V) (w : Fin ℓ → ℚ) : V → ℚ :=
  fun v => ∑ i : Fin ℓ,
    if v = P (Fin.castSucc i) then w i
    else if v = P (Fin.succ i) then -w i
    else 0

/-- The oriented endpoint boundary `[P₀] - [Pₗ]`. -/
def pathEndpointBoundary {V : Type*} [DecidableEq V] {ℓ : ℕ}
    (P : Fin (ℓ + 1) → V) : V → ℚ :=
  fun v =>
    if v = P 0 then 1
    else if v = P (Fin.last ℓ) then -1
    else 0

/--
The coefficient-jump identity for the residual supply of a rational path
chain.  Integral `u` records exactly the packet's choice of an `N` clearing
all denominators.
-/
def residualSupplyFromCoefficientJumpsClaim : Prop := by
  classical
  exact ∀ {V : Type*} [Fintype V] [DecidableEq V] (ℓ : ℕ),
    ∀ (hℓ : 0 < ℓ),
    ∀ (P : Fin (ℓ + 1) → V), Function.Injective P →
      ∀ (q : Fin ℓ → ℚ), (∀ i, 0 ≤ q i) →
        ∀ (N : ℕ) (u : Fin ℓ → ℤ),
          1 ≤ N →
          (∀ i : Fin ℓ, (N : ℚ) * q i = (u i : ℚ)) →
          let p : Fin ℓ → ℚ := fun _ => 1
          let b : V → ℚ := pathEndpointBoundary P
          let d : V → ℚ :=
            fun v => (N : ℚ) * b v - pathIncidence P (fun i => (u i : ℚ)) v
          (∑ v : V, d v = 0) ∧
            (∀ v : V, (∀ k : Fin (ℓ + 1), v ≠ P k) → d v = 0) ∧
            d (P 0) = (N : ℚ) - (u ⟨0, hℓ⟩ : ℚ) ∧
            (∀ (i : Fin ℓ) (hi : i.val + 1 < ℓ),
              d (P (Fin.succ i)) =
                (u i : ℚ) - (u ⟨i.val + 1, hi⟩ : ℚ)) ∧
            (∃ (i : Fin ℓ) (hi : i.val + 1 = ℓ),
              d (P (Fin.last ℓ)) = (u i : ℚ) - (N : ℚ))

end MathlibPlus.Open.ResearchFormalize
