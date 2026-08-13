import Mathlib.Logic.Relation
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.Order.SetNotation

namespace MathlibPlus.Combinatorics

/-!
The exact reachable-set/Boolean-cut component of admitted claim 50520.
The source's incidence notation is represented by `φ (tail e) - φ (head e)`;
for an incidence column `e_tail - e_head` this is exactly the corresponding
coordinate of `Dᵀφ`.
-/

private def edgeRel {V E : Type*} (tail head : E → V) (u v : V) : Prop :=
  ∃ e, tail e = u ∧ head e = v

private def reachable {V E : Type*} (tail head : E → V) (α v : V) : Prop :=
  Relation.ReflTransGen (edgeRel tail head) α v

private def forwardClosed {V E : Type*} (tail head : E → V) (S : Set V) : Prop :=
  ∀ e, tail e ∈ S → head e ∈ S

private def separating {V E : Type*} (tail head : E → V) (α ω : V) (S : Set V) : Prop :=
  α ∈ S ∧ ω ∉ S ∧ forwardClosed tail head S

private noncomputable def booleanCutIndicator
    {V E : Type*} (tail head : E → V) (α : V) : V → ℤ := by
  classical
  exact fun v => if reachable tail head α v then 0 else 1

/-- If the sink is unreachable, its reachable set is the canonical smallest
forward-closed separator, and its complement indicator is the coefficient-one
Boolean/Farkas witness from claim 50520. -/
theorem canonicalReachableCut_claim50520
    {V E : Type*} [Fintype V] [Fintype E]
    (tail head : E → V) (α ω : V)
    (hω : ¬ reachable tail head α ω) :
    let R : Set V := {v | reachable tail head α v}
    let φ : V → ℤ := booleanCutIndicator tail head α
    α ∈ R ∧
      ω ∉ R ∧
      forwardClosed tail head R ∧
      R = ⋂₀ {S : Set V | separating tail head α ω S} ∧
      (∀ e, 0 ≤ φ (tail e) - φ (head e)) ∧
      φ α - φ ω = -1 := by
  classical
  let R : Set V := {v | reachable tail head α v}
  let φ : V → ℤ := booleanCutIndicator tail head α
  have hα : α ∈ R := by
    exact Relation.ReflTransGen.refl
  have hω' : ω ∉ R := by
    exact hω
  have hclosed : forwardClosed tail head R := by
    intro e he
    exact Relation.ReflTransGen.tail he ⟨e, rfl, rfl⟩
  have hRsep : separating tail head α ω R := ⟨hα, hω', hclosed⟩
  have hRsub : ∀ S : Set V, separating tail head α ω S → R ⊆ S := by
    intro S hS v hv
    rcases hS with ⟨hαS, hωS, hclosedS⟩
    induction hv with
    | refl => exact hαS
    | @tail b c hv hbc ih =>
        rcases hbc with ⟨e, rfl, rfl⟩
        exact hclosedS e ih
  have hsmallest : R = ⋂₀ {S : Set V | separating tail head α ω S} := by
    apply Set.Subset.antisymm
    · apply Set.subset_sInter
      intro S hS
      exact hRsub S hS
    · exact Set.sInter_subset_of_mem hRsep
  have hineq : ∀ e, 0 ≤ φ (tail e) - φ (head e) := by
    intro e
    by_cases ht : tail e ∈ R
    · have hh : head e ∈ R := hclosed e ht
      have ht' : reachable tail head α (tail e) := ht
      have hh' : reachable tail head α (head e) := hh
      simp [φ, booleanCutIndicator, ht', hh']
    · by_cases hh : head e ∈ R
      · have ht' : ¬ reachable tail head α (tail e) := ht
        have hh' : reachable tail head α (head e) := hh
        simp [φ, booleanCutIndicator, ht', hh']
      · have ht' : ¬ reachable tail head α (tail e) := ht
        have hh' : ¬ reachable tail head α (head e) := hh
        simp [φ, booleanCutIndicator, ht', hh']
  have hdiff : φ α - φ ω = -1 := by
    have hα' : reachable tail head α α := hα
    have hω'' : ¬ reachable tail head α ω := hω'
    simp [φ, booleanCutIndicator, hα', hω'']
  exact ⟨hα, hω', hclosed, hsmallest, hineq, hdiff⟩

end MathlibPlus.Combinatorics
