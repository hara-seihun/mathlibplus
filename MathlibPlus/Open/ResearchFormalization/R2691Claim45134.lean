import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R2691Claim45134

open scoped BigOperators

noncomputable section

/-- A finite family of finite sets, with finiteness carried by the family and
its members rather than by an ambient ground type. -/
abbrev Family (X : Type*) := Finset (Finset X)

def unionClosed {X : Type*} [DecidableEq X]
    (F : Family X) : Prop :=
  ∀ ⦃A B : Finset X⦄, A ∈ F → B ∈ F → A ∪ B ∈ F

def upperFamily {X : Type*} [DecidableEq X]
    (F : Family X) (M : Finset X) : Finset (Finset X) :=
  F.filter (fun G => M ⊆ G)

/-- The trace fibre indexed by a member of the upper family. -/
def traceFamily {X : Type*} [DecidableEq X]
    (F : Family X) (M G : Finset X) : Finset (Finset X) :=
  (F.filter (fun A => A ∪ M = G)).image (fun A => A ∩ M)

def frequency {X : Type*} [DecidableEq X]
    (F : Family X) (x : X) : ℤ :=
  (F.filter (fun A => x ∈ A)).card

def properTraceFrequency {X : Type*} [DecidableEq X]
    (H : Finset (Finset X)) (M : Finset X) (x : X) : ℤ :=
  (H.filter (fun S => S ≠ M ∧ x ∈ S)).card

def floorHalfMinusOne (δ : ℤ) : ℤ :=
  Int.floor (((δ - 1 : ℤ) : ℚ) / 2)

/-- Claim R-2691.2: the exact deficit and coordinate-incidence ledger on
union-with-`M` trace fibres.  Coordinate-indexed assertions are quantified
only for coordinates in `M`; the proper-empty-trace and incidence bounds are
kept outside the no-abundant-coordinate implication. -/
def claim45134 : Prop :=
  ∀ {X : Type*} [DecidableEq X]
    (F : Family X) (M : Finset X),
    M ∈ F →
    unionClosed F →
      let U := upperFamily F M
      let H := traceFamily F M
      let a : ℤ := U.card
      let m : ℤ := F.card
      let k : Finset X → ℤ := fun G => (H G).card - 1
      let δ : ℤ := m - 2 * a
      let p : X → ℤ := fun x =>
        (F.filter (fun A => ¬ M ⊆ A ∧ x ∈ A)).card
      let f : X → ℤ := fun x => frequency F x
      (m = ∑ G ∈ U, ((H G).card : ℤ)) ∧
        (δ = ∑ G ∈ U, ((H G).card : ℤ) - 2) ∧
        (δ = ∑ G ∈ U, k G - 1) ∧
        (∀ x : X, x ∈ M → f x = a + p x) ∧
        (∀ x : X, x ∈ M →
          p x = ∑ G ∈ U, properTraceFrequency (H G) M x) ∧
        (∀ G : Finset X, G ∈ U →
          ((H G).filter (fun S => S ≠ M ∧ S = ∅)).card ≤ 1) ∧
        (∑ x ∈ M, p x ≥ δ) ∧
        ((∀ x : X, x ∈ M → 2 * f x < m) →
          (∀ x : X, x ∈ M →
            2 * (a + p x) < m ∧
              m = 2 * a + δ ∧
              p x ≤ floorHalfMinusOne δ))

end

end MathlibPlus.Open.ResearchFormalization.R2691Claim45134
