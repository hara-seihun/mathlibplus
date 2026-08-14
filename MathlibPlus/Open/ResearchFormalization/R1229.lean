import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R1229

/-- The group presentation used for the dicyclic group of order twelve. -/
def q12Presentation (Q : Type*) [Group Q] [Fintype Q] (a b : Q) : Prop :=
  Fintype.card Q = 12 ∧
    Subgroup.closure ({a, b} : Set Q) = ⊤ ∧
    a ^ 6 = 1 ∧
    b ^ 2 = a ^ 3 ∧
    b⁻¹ * a * b = a⁻¹

def q12C2 (Q : Type*) [Group Q] (a : Q) : Subgroup Q :=
  Subgroup.closure ({a ^ 3} : Set Q)

def q12C3 (Q : Type*) [Group Q] (a : Q) : Subgroup Q :=
  Subgroup.closure ({a ^ 2} : Set Q)

def q12C6 (Q : Type*) [Group Q] (a : Q) : Subgroup Q :=
  Subgroup.closure ({a} : Set Q)

def q12C4 (Q : Type*) [Group Q] (a b : Q) (i : Fin 3) : Subgroup Q :=
  Subgroup.closure ({a ^ i.val * b} : Set Q)

def conjugateSubgroup {Q : Type*} [Group Q]
    (H K : Subgroup Q) : Prop :=
  ∃ g : Q, ∀ x : Q, x ∈ H ↔ g * x * g⁻¹ ∈ K

/-- The complete subgroup list for a group carrying the stated order-twelve
presentation.  The explicit normal-form representatives make the three
exceptional order-four subgroups part of the statement. -/
def claim30351 : Prop :=
  ∀ (Q : Type*) [Group Q] [Fintype Q] (a b : Q),
    q12Presentation Q a b →
      (∀ H : Subgroup Q,
        H = ⊥ ∨
        H = q12C2 Q a ∨
        H = q12C3 Q a ∨
        H = q12C6 Q a ∨
        H = ⊤ ∨
        ∃ i : Fin 3, H = q12C4 Q a b i) ∧
      Nat.card (q12C2 Q a) = 2 ∧
      Nat.card (q12C3 Q a) = 3 ∧
      Nat.card (q12C6 Q a) = 6 ∧
      (∀ z : Q, z ∈ q12C2 Q a → ∀ x : Q, z * x = x * z) ∧
      (∀ i : Fin 3, Nat.card (q12C4 Q a b i) = 4) ∧
      (∀ i j : Fin 3, i ≠ j → q12C4 Q a b i ≠ q12C4 Q a b j) ∧
      (∀ i : Fin 3, conjugateSubgroup (q12C4 Q a b i) (q12C4 Q a b 0)) ∧
      (∀ H : Subgroup Q,
        H.Normal ↔ ∀ i : Fin 3, H ≠ q12C4 Q a b i) ∧
      q12C4 Q a b 0 ⊓ q12C4 Q a b 1 ⊓ q12C4 Q a b 2 = q12C2 Q a

/-- The direct-product subgroup appearing in the splitting assertion. -/
def directProductSubgroup {A Q : Type*} [Group A] [Group Q]
    (C : Subgroup A) (U : Subgroup Q) : Subgroup (A × Q) where
  carrier := {z | z.1 ∈ C ∧ z.2 ∈ U}
  one_mem' := ⟨C.one_mem, U.one_mem⟩
  mul_mem' := by
    intro x y hx hy
    exact ⟨C.mul_mem hx.1 hy.1, U.mul_mem hx.2 hy.2⟩
  inv_mem' := by
    intro x hx
    exact ⟨C.inv_mem hx.1, U.inv_mem hx.2⟩

/-- Coprime direct-product subgroup splitting for the order-twelve factor. -/
def claim30352 : Prop :=
  ∀ (A Q : Type*) [CommGroup A] [Fintype A] [Group Q] [Fintype Q]
    (a b : Q),
    q12Presentation Q a b →
      Nat.Coprime (Fintype.card A) 12 →
      ∀ H : Subgroup (A × Q),
        ∃ C : Subgroup A, ∃ U : Subgroup Q,
          H = directProductSubgroup C U

end MathlibPlus.Open.ResearchFormalization.R1229
