import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic

open scoped BigOperators

namespace MathlibPlus.Algebra.Claim17423

/-- Vertices of the finite path `v₀, ..., v_N`. -/
abbrev VertexChain (R : Type*) (N : ℕ) := Fin (N + 1) → R

/-- Oriented edges of the finite path `a_j : v_j ⟶ v_(j+1)`. -/
abbrev EdgeChain (R : Type*) (N : ℕ) := Fin N → R

/-- The signed vertex chain which is the boundary of one oriented edge. -/
def edgeBoundary {R : Type*} [AddCommGroup R] {N : ℕ} (j : Fin N) (r : R) :
    VertexChain R N :=
  fun v => if v = j.succ then r else if v = j.castSucc then -r else 0

/-- The boundary of an edge chain on the finite path. -/
def pathBoundary {R : Type*} [AddCommGroup R] {N : ℕ} (a : EdgeChain R N) :
    VertexChain R N :=
  fun v => ∑ j, edgeBoundary j (a j) v

/-- The total mass of an event (vertex) chain. -/
def eventMass {R : Type*} [AddCommGroup R] {N : ℕ} (e : VertexChain R N) : R :=
  ∑ v, e v

/-- An event chain has zero mass precisely when its coefficient sum vanishes. -/
def IsZeroMass {R : Type*} [AddCommGroup R] {N : ℕ} (e : VertexChain R N) : Prop :=
  eventMass e = 0

@[simp] theorem edgeBoundary_mass_zero {R : Type*} [AddCommGroup R]
    {N : ℕ} (j : Fin N) (r : R) :
    eventMass (edgeBoundary j r) = 0 := by
  classical
  have hne : j.succ ≠ j.castSucc := by
    intro h
    have hv := congrArg Fin.val h
    simp at hv
  have hsplit (v : Fin (N + 1)) :
      (if v = j.succ then r else if v = j.castSucc then -r else 0) =
        (if v = j.succ then r else 0) + (if v = j.castSucc then -r else 0) := by
    by_cases h₁ : v = j.succ <;> by_cases h₂ : v = j.castSucc <;>
      simp [h₁, h₂, hne, Ne.symm hne]
  simp only [eventMass, edgeBoundary]
  simp_rw [hsplit]
  rw [Finset.sum_add_distrib]
  simp [Finset.sum_ite_eq']

/-- Every path boundary has total vertex mass zero. -/
theorem pathBoundary_mass_zero {R : Type*} [AddCommGroup R]
    {N : ℕ} (a : EdgeChain R N) :
    eventMass (pathBoundary a) = 0 := by
  classical
  simp only [eventMass, pathBoundary]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro j hj
  exact edgeBoundary_mass_zero j (a j)

end MathlibPlus.Algebra.Claim17423
