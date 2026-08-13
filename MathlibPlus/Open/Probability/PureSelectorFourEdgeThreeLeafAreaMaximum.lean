import Mathlib

namespace MathlibPlus.Open.Probability

open scoped BigOperators

noncomputable section

/-- Exact finite pure-selector four-edge/three-leaf area census interface.

The local carriers are the seven independent Boolean coordinates, the selector
mixture, complete fresh-coordinate policies represented by their transcript
choice function, and the root-inclusive expected posterior-variance area.
The universal and sharp clauses are kept as one registry proposition. -/
def pureSelectorFourEdgeThreeLeafAreaMaximum : Prop :=
  let root : Fin 4 → Fin 7 := fun e => ⟨e.1, by omega⟩
  let leaf : Fin 3 → Fin 7 := fun l => ⟨4 + l.1, by omega⟩
  let State := Fin 7 → Option Bool
  let Policy := State → Fin 7
  let sign : Bool → ℚ := fun b => if b then 1 else -1
  let selector : (Fin 4 → Fin 3) → (Fin 4 → Fin 3) →
      (Fin 7 → Bool) → Fin 4 → ℚ :=
    fun u v x e => if x (root e) then sign (x (leaf (v e)))
      else sign (x (leaf (u e)))
  let mixture : (Fin 4 → Fin 3) → (Fin 4 → Fin 3) →
      (Fin 7 → Bool) → ℚ :=
    fun u v x => (1 / 4 : ℚ) * ∑ e, selector u v x e
  let valid : Policy → Prop := fun P =>
    ∀ s : State, (∃ i, s i = none) → s (P s) = none
  let reveal : State → Fin 7 → Bool → State :=
    fun s i b => Function.update s i (some b)
  let stateAt : Policy → (Fin 7 → Bool) → ℕ → State :=
    fun P x k =>
      Nat.rec (fun _ : Fin 7 => none)
        (fun _ s => reveal s (P s) (x (P s))) k
  let cell : State → Finset (Fin 7 → Bool) := fun s =>
    Finset.univ.filter (fun x => ∀ i, s i = some (x i))
  let mean : (Fin 4 → Fin 3) → (Fin 4 → Fin 3) → State → ℚ :=
    fun u v s =>
      if h : (cell s).Nonempty then
        (∑ x in cell s, mixture u v x) / (cell s).card
      else 0
  let conditionalVariance : (Fin 4 → Fin 3) → (Fin 4 → Fin 3) →
      State → ℚ :=
    fun u v s =>
      if h : (cell s).Nonempty then
        (∑ x in cell s, (mixture u v x - mean u v s) ^ 2) / (cell s).card
      else 0
  let area : (Fin 4 → Fin 3) → (Fin 4 → Fin 3) → Policy → ℚ :=
    fun u v P =>
      (1 / (Fintype.card (Fin 7 → Bool) : ℚ)) *
        ∑ x, ∑ k in Finset.range 7,
          conditionalVariance u v (stateAt P x k)
  let u₀ : Fin 4 → Fin 3 := fun _ => 0
  let v₀ : Fin 4 → Fin 3 := fun _ => 1
  (∀ (u v : Fin 4 → Fin 3), (∀ e, u e ≠ v e) →
      ∃ P : Policy, valid P ∧ area u v P ≤ 21 / 16) ∧
    (∀ P : Policy, valid P → 21 / 16 ≤ area u₀ v₀ P)

end
end MathlibPlus.Open.Probability
