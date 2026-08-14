import Mathlib

namespace MathlibPlus.Open.ResearchFormalization

/-- The augmented reachability predicate used for the sink `ω`. -/
def augmentedGoal {V : Type*} (E : V → V → Prop) (S_ent X_rk1 : Set V) : Prop :=
  ∃ s, s ∈ S_ent ∧
    Relation.ReflTransGen
      (fun u v : Option V =>
        match u, v with
        | some x, some y => E x y
        | some x, none => x ∈ X_rk1
        | none, _ => False)
      (some s) none

/-- States reachable from an entered source by internal edges. -/
def reachableStates {V : Type*} (E : V → V → Prop) (S_ent : Set V) : Set V :=
  {v | ∃ s, s ∈ S_ent ∧ Relation.ReflTransGen E s v}

/-- Minimality for the natural-valued filtration on the reachable states. -/
def reachableMuMinimal {V : Type*} (μ : V → ℕ) (R : Set V) (v : V) : Prop :=
  v ∈ R ∧ ∀ w, w ∈ R → μ v ≤ μ w

/-- The local-extension condition from the source-specific theorem. -/
def localExtensionCondition {V : Type*} (E : V → V → Prop)
    (R X_rk1 : Set V) : Prop :=
  ∀ v, v ∈ R → v ∉ X_rk1 → ∃ w, E v w

/-- R-4022, S4: failure of the augmented existential path leaves a reachable
minimal non-rank-one terminal state. -/
def claim51888 {V : Type*} (E : V → V → Prop) (μ : V → ℕ)
    (S_ent X_rk1 : Set V) : Prop :=
  S_ent.Nonempty →
    (∀ v w, E v w → μ w < μ v) →
    ¬ augmentedGoal E S_ent X_rk1 →
    ∀ v, reachableMuMinimal μ (reachableStates E S_ent) v →
      v ∉ X_rk1 ∧ ∀ w, ¬ E v w

/-- R-4022, S5: the local extension condition is sufficient for the
source-specific existential goal. -/
def claim51890 {V : Type*} (E : V → V → Prop) (μ : V → ℕ)
    (S_ent X_rk1 : Set V) : Prop :=
  S_ent.Nonempty →
    (∀ v w, E v w → μ w < μ v) →
    localExtensionCondition E (reachableStates E S_ent) X_rk1 →
    augmentedGoal E S_ent X_rk1

/-- R-4022, S6: the explicit three-state counterexample. -/
def claim51891 : Prop :=
  let V := Fin 3
  let E : V → V → Prop := fun v w =>
    (v = 0 ∧ w = 1) ∨ (v = 0 ∧ w = 2)
  let μ : V → ℕ := fun v => if v = 0 then 1 else 0
  let S_ent : Set V := {0}
  let X_rk1 : Set V := {1}
  let R := reachableStates E S_ent
  S_ent.Nonempty ∧
    (∀ v w, E v w → μ w < μ v) ∧
    augmentedGoal E S_ent X_rk1 ∧
    (2 : V) ∈ R ∧
    (2 : V) ∉ X_rk1 ∧
    (∀ w, ¬ E (2 : V) w) ∧
    ¬ localExtensionCondition E R X_rk1

end MathlibPlus.Open.ResearchFormalization
