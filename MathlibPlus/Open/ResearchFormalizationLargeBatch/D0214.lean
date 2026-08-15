import Mathlib

open scoped BigOperators
open scoped Topology
open MeasureTheory
open Set
open Filter

namespace MathlibPlus.Open.ResearchFormalizationLargeBatch
def claim6492_generalPairedGaleRowConstruction : Prop := by
  classical
  exact ∀ (p m : ℕ) (hp : Nat.Prime p), p % 2 = 1 →
    letI : Fact (Nat.Prime p) := ⟨hp⟩
    ∀ (A B : Type*)
    [AddCommGroup A] [AddCommGroup B]
    [Module (ZMod p) A] [Module (ZMod p) B]
    [FiniteDimensional (ZMod p) A] [FiniteDimensional (ZMod p) B],
    ∀ (d : Fin m → B) (u : Fin m → (A →ₗ[ZMod p] ZMod p))
      (c : Fin m → ZMod p),
      (∀ i, d i ≠ 0 ∨ u i ≠ 0) →
      let R_i : Fin m → ZMod p → Set (A × B) :=
        fun i ci => {q | q.2 = d i ∧ u i q.1 = ci}
      let S_c : (Fin m → ZMod p) → Set (A × B) := fun cc =>
        ⋃ i, (R_i i (cc i) ∪ {q | -q ∈ R_i i (cc i)})
      ∀ q, q ∈ S_c c ↔
        ∃ i, (q.2 = d i ∧ u i q.1 = c i) ∨
          ((-q).2 = d i ∧ u i (-q).1 = c i)

def claim6493_pairedConnectionSetsInverseClosed : Prop := by
  classical
  exact ∀ (p m : ℕ) (hp : Nat.Prime p), p % 2 = 1 →
    letI : Fact (Nat.Prime p) := ⟨hp⟩
    ∀ (A B : Type*)
    [AddCommGroup A] [AddCommGroup B]
    [Module (ZMod p) A] [Module (ZMod p) B]
    [FiniteDimensional (ZMod p) A] [FiniteDimensional (ZMod p) B],
    ∀ (d : Fin m → B) (u : Fin m → (A →ₗ[ZMod p] ZMod p))
      (c : Fin m → ZMod p),
      (∀ i, d i ≠ 0 ∨ u i ≠ 0) →
      let R_i : Fin m → ZMod p → Set (A × B) :=
        fun i ci => {q | q.2 = d i ∧ u i q.1 = ci}
      let S_c : (Fin m → ZMod p) → Set (A × B) := fun cc =>
        ⋃ i, (R_i i (cc i) ∪ {q | -q ∈ R_i i (cc i)})
      ∀ cc q, q ∈ S_c cc → -q ∈ S_c cc

def claim6494_constantLabelledDifferencesGiveOddShearIsomorphism : Prop := by
  classical
  exact ∀ (p m : ℕ) (hp : Nat.Prime p), p % 2 = 1 →
    letI : Fact (Nat.Prime p) := ⟨hp⟩
    ∀ (A B : Type*)
    [AddCommGroup A] [AddCommGroup B]
    [Module (ZMod p) A] [Module (ZMod p) B]
    [FiniteDimensional (ZMod p) A] [FiniteDimensional (ZMod p) B],
    ∀ (d : Fin m → B) (u : Fin m → (A →ₗ[ZMod p] ZMod p))
      (lam : Fin m → ZMod p) (s : B → A),
      (∀ i, d i ≠ 0 ∨ u i ≠ 0) →
      (∀ x, s (-x) = -s x) →
      (∀ i x, u i (s (x + d i) - s x) = lam i) →
      let R_i : Fin m → ZMod p → Set (A × B) :=
        fun i ci => {q | q.2 = d i ∧ u i q.1 = ci}
      let S_c : (Fin m → ZMod p) → Set (A × B) := fun cc =>
        ⋃ i, (R_i i (cc i) ∪ {q | -q ∈ R_i i (cc i)})
      let θ : A × B → A × B := fun q => (q.1 + s q.2, q.2)
      Function.Bijective θ ∧
        (∀ v w, w - v ∈ S_c 0 ↔ θ w - θ v ∈ S_c lam)

end MathlibPlus.Open.ResearchFormalizationLargeBatch
