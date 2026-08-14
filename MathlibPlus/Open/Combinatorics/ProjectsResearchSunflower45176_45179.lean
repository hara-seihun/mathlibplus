import Mathlib

open scoped BigOperators Classical
noncomputable section

namespace MathlibPlus.Open.ProjectsResearch

/-- The local Boolean factor used by the 0,1,k condition. -/
def localSunflowerFactor (k : ℕ) (S : Finset (Fin k)) : ℚ :=
  if S.card ≤ 1 ∨ S.card = k then 1 else 0

def sunflowerTuple {k n : ℕ}
    (A : Fin k → Finset (Fin n)) : Prop :=
  ∃ C : Finset (Fin n),
    (∀ i, C ⊆ A i) ∧
      (∀ i j, i ≠ j → Disjoint (A i \ C) (A j \ C))

def sunflowerFreeFamily {k n : ℕ}
    (F : Finset (Finset (Fin n))) : Prop :=
  ¬ ∃ A : Fin k → Finset (Fin n),
      (∀ i, A i ∈ F) ∧
      Pairwise (fun i j => A i ≠ A j) ∧
      sunflowerTuple A

def sunflowerTensorValue {k n : ℕ}
    (A : Fin k → Finset (Fin n)) : ℚ :=
  ∏ x : Fin n,
    localSunflowerFactor k (Finset.univ.filter (fun i => x ∈ A i))

/-- Claim R-2797.1 (45176). -/
def claim45176 : Prop :=
  ∀ k n : ℕ, 3 ≤ k → 1 ≤ n →
    ∀ F : Finset (Finset (Fin n)),
      (∀ A ∈ F, A.card = k) →
      sunflowerFreeFamily (k := k) F →
      ∀ A : Fin k → Finset (Fin n),
        (∀ i, A i ∈ F) →
        (sunflowerTensorValue A = 1 ↔
          ∀ i j, A i = A j)

/-! The concrete 5-cycle family used in Claim R-2797.3. -/

def c5Edge45179 (i : Fin 5) : Finset (Fin 5) :=
  match i with
  | ⟨0, _⟩ => {0, 1}
  | ⟨1, _⟩ => {1, 2}
  | ⟨2, _⟩ => {2, 3}
  | ⟨3, _⟩ => {3, 4}
  | ⟨4, _⟩ => {4, 0}

def c5Family45179 : Finset (Finset (Fin 5)) :=
  (Finset.univ.image c5Edge45179)

def c5Incidence45179 : Matrix (Fin 5) (Fin 5) ℚ :=
  fun e v => if v ∈ c5Edge45179 e then 1 else 0

def c5ContainmentFunction45179 (e : Fin 5) : Fin 5 → ℚ :=
  fun v => if v ∈ c5Edge45179 e then 1 else 0

def c5ConstantFunction45179 : Fin 5 → ℚ := fun _ => 1

def c5NoThreeSunflower45179 : Prop :=
  sunflowerFreeFamily (k := 3) (n := 5) c5Family45179

def c5ContainmentSpan45179 : Submodule ℚ (Fin 5 → ℚ) :=
  Submodule.span ℚ (Set.range c5ContainmentFunction45179)

/-- Claim R-2797.3 (45179), including the exact incidence certificate and
its rank consequence. -/
def claim45179 : Prop :=
  (∀ e ∈ c5Family45179, (e.card = 2)) ∧
    c5Family45179.card = 5 ∧
    c5NoThreeSunflower45179 ∧
    Matrix.det c5Incidence45179 = 2 ∧
    Matrix.rank c5Incidence45179 = 5 ∧
    c5ConstantFunction45179 ∈ c5ContainmentSpan45179 ∧
    c5ConstantFunction45179 =
      (1 / 2 : ℚ) • (∑ e : Fin 5, c5ContainmentFunction45179 e) ∧
    Module.finrank ℚ c5ContainmentSpan45179 = 5 ∧
    (1 + Nat.choose 2 1 = 3) ∧
    (5 ≠ 3)

end MathlibPlus.Open.ProjectsResearch
