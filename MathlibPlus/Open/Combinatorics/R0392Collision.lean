import Mathlib

open Classical

namespace MathlibPlus.Open.Combinatorics.R0392

noncomputable section

/-- The common intersection core of a three-member sunflower. -/
def sunflowerWithCore {V : Type*} [DecidableEq V]
    (F : Fin 3 → Finset V) (core : Finset V) : Prop :=
  (∀ i : Fin 3, core ⊆ F i) ∧
    ∀ i j : Fin 3, i ≠ j → F i ∩ F j = core

/-- A three-member sunflower with an unspecified core. -/
def isSunflower {V : Type*} [DecidableEq V]
    (F : Fin 3 → Finset V) : Prop :=
  ∃ core : Finset V, sunflowerWithCore F core

/-- Exact-membership cells of an ordered triple on an ambient finite set. -/
def cellCount {V : Type*} [DecidableEq V]
    (U : Finset V) (F : Fin 3 → Finset V)
    (S : Finset (Fin 3)) : ℕ :=
  (U.filter (fun z => ∀ i : Fin 3, i ∈ S ↔ z ∈ F i)).card

/-- The intersection margin indexed by a nonempty or singleton/pair trace. -/
def intersectionMargin {V : Type*} [DecidableEq V]
    (U : Finset V) (F : Fin 3 → Finset V)
    (T : Finset (Fin 3)) : ℕ :=
  (U.filter (fun z => ∀ i ∈ T, z ∈ F i)).card

/-- The all-uniform sunflower/non-sunflower collision realizes the primitive
three-cell trade. -/
def claim_20849 : Prop :=
  ∀ (n : ℕ), 2 ≤ n →
    ∀ {V : Type*} [DecidableEq V]
      (U C : Finset V) (a b c d : V),
      C ⊆ U →
        U.card = n + 2 →
          C.card = n - 2 →
            a ∈ U ∧ b ∈ U ∧ c ∈ U ∧ d ∈ U ∧
              a ∉ C ∧ b ∉ C ∧ c ∉ C ∧ d ∉ C ∧
                a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d →
                  let first : Fin 3 → Finset V :=
                    ![C ∪ {a, b}, C ∪ {a, c}, C ∪ {a, d}]
                  let second : Fin 3 → Finset V :=
                    ![C ∪ {a, b}, C ∪ {a, c}, C ∪ {b, c}]
                  Function.Injective first ∧
                    Function.Injective second ∧
                    first ≠ second ∧
                    (∀ i : Fin 3,
                      (first i).card = n ∧ (second i).card = n) ∧
                    (∀ i : Fin 3,
                      intersectionMargin U first {i} = n ∧
                        intersectionMargin U second {i} = n) ∧
                    (∀ i j : Fin 3, i ≠ j →
                      intersectionMargin U first {i, j} = n - 1 ∧
                        intersectionMargin U second {i, j} = n - 1) ∧
                    sunflowerWithCore first (C ∪ {a}) ∧
                    ¬ isSunflower second ∧
                    (∀ S : Finset (Fin 3),
                      (cellCount U first S : ℤ) - cellCount U second S =
                        (-1 : ℤ) ^ (3 - S.card))

end

end MathlibPlus.Open.Combinatorics.R0392
