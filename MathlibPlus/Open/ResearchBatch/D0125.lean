import Mathlib

namespace MathlibPlus.Open.ResearchBatch.D0125

open scoped BigOperators Classical
noncomputable section

def coordinateVector {F S : Type*} [Field F] [DecidableEq S]
    (i : S) : S → F := fun j => if j = i then 1 else 0

def claim_5703
    {F S B ι : Type*} [Field F] [Fintype S] [Fintype B]
    (R : Submodule F (S → F)) (R_b : B → Submodule F (S → F))
    (D : ι → Submodule F (S → F)) : Prop :=
  R = ⨆ b, R_b b ∧
    (∀ b, Module.Finite F (R_b b)) ∧
      (∀ r, D r ≤ R)

def claim_5704
    {F S : Type*} [Field F] [Fintype S] [DecidableEq S]
    (D : Submodule F (S → F)) : Prop :=
  (∀ i : S, ∀ a : F, a ≠ 0 →
    a • coordinateVector i ∈ D →
      Submodule.mkQ D (coordinateVector i) = 0) ∧
    (∀ i j : S, i ≠ j → ∀ a b : F, a ≠ 0 → b ≠ 0 →
      a • coordinateVector i + b • coordinateVector j ∈ D →
        Submodule.mkQ D (coordinateVector i) =
          (-(b / a)) • Submodule.mkQ D (coordinateVector j))

def hammingCount {α β : Type*} [Fintype α] [DecidableEq β]
    (f g : α → β) : Nat :=
  (Finset.univ.filter (fun x => f x ≠ g x)).card

def badPoints {G : Type*} {n : Nat} [Group G] [Fintype G] [DecidableEq G]
    (Φ : G → Equiv.Perm (Fin n)) : Finset (Fin n) :=
  Finset.univ.filter (fun x => ∃ g h : G, Φ g (Φ h x) ≠ Φ (g * h) x)

def normalizedPermutationDistance {n : Nat}
    (f g : Equiv.Perm (Fin n)) : ℚ :=
  (hammingCount (f : Fin n → Fin n) (g : Fin n → Fin n) : ℚ) / (n : ℚ)

def tableDefect {G : Type*} {n : Nat} [Group G] [Fintype G] [DecidableEq G]
    (Φ : G → Equiv.Perm (Fin n)) (g h : G) : ℚ :=
  (hammingCount (fun x => Φ g (Φ h x)) (fun x => Φ (g * h) x) : ℚ) / (n : ℚ)

def averageRepairDistance {G : Type*} {n : Nat} [Group G] [Fintype G] [DecidableEq G]
    (Φ Ψ : G → Equiv.Perm (Fin n)) : ℚ :=
  (∑ g : G, normalizedPermutationDistance (Φ g) (Ψ g)) /
    (Fintype.card G : ℚ)

def averageCompleteTableDefect {G : Type*} {n : Nat} [Group G] [Fintype G] [DecidableEq G]
    (Φ : G → Equiv.Perm (Fin n)) : ℚ :=
  (∑ g : G, ∑ h : G, tableDefect Φ g h) /
    (Fintype.card G : ℚ) ^ 2

def claim_5713
    {G : Type*} {n : Nat} [Group G] [Fintype G] [DecidableEq G]
    (Φ : G → Equiv.Perm (Fin n)) : Prop :=
  let B := badPoints Φ
  (∀ g : G, ∀ x : Fin n,
      (x ∈ B ↔ Φ g x ∈ B)) ∧
    ∃ Ψ : G → Equiv.Perm (Fin n),
      (∀ g h : G, ∀ x : Fin n, Ψ g (Ψ h x) = Ψ (g * h) x) ∧
        (∀ g : G, ∀ x : Fin n, x ∉ B → Ψ g x = Φ g x) ∧
          (∀ g : G, ∀ x : Fin n, x ∈ B → Ψ g x = x) ∧
            averageRepairDistance Φ Ψ ≤
              (Fintype.card G : ℚ) ^ 2 * averageCompleteTableDefect Φ

def isInvolution {n : Nat} (τ : Equiv.Perm (Fin n)) : Prop :=
  τ.trans τ = Equiv.refl (Fin n)

def c2Action {n : Nat} (e a : Equiv.Perm (Fin n)) : Prop :=
  e = Equiv.refl (Fin n) ∧ isInvolution a

def c2A {n : Nat} (u : Equiv.Perm (Fin n)) : Nat :=
  hammingCount (u : Fin n → Fin n) (Equiv.refl (Fin n) : Fin n → Fin n)

def c2B {n : Nat} (u v : Equiv.Perm (Fin n)) : Nat :=
  hammingCount (v.trans v : Fin n → Fin n) (u : Fin n → Fin n)

def c2RepairDistance {n : Nat}
    (u v e a : Equiv.Perm (Fin n)) : ℚ :=
  (hammingCount (u : Fin n → Fin n) (e : Fin n → Fin n) +
      hammingCount (v : Fin n → Fin n) (a : Fin n → Fin n) : ℚ) /
    (2 * n : ℚ)

def c2DefectDistance {n : Nat} (u v : Equiv.Perm (Fin n)) : ℚ :=
  (3 * c2A u + c2B u v : ℚ) / (4 * n : ℚ)

def claim_5715 : Prop :=
  (∀ n : Nat, ∀ u v : Equiv.Perm (Fin n),
    ∃ e a : Equiv.Perm (Fin n),
      c2Action e a ∧
        let C := hammingCount (u : Fin n → Fin n) (e : Fin n → Fin n) +
          hammingCount (v : Fin n → Fin n) (a : Fin n → Fin n)
        let A := c2A u
        let B := c2B u v
        let V := 3 * A + B
        C ≤ (5 * A + 2 * B) / 3 ∧ 3 * C ≤ 2 * V) ∧
    (∀ n : Nat, ∀ u v : Equiv.Perm (Fin n),
      ∃ e a : Equiv.Perm (Fin n),
        c2Action e a ∧
          c2RepairDistance u v e a ≤
            (4 / 3 : ℚ) * c2DefectDistance u v) ∧
    (∀ c : ℚ, c < (4 / 3 : ℚ) →
      ∃ n : Nat, 0 < n ∧
        ∃ u v : Equiv.Perm (Fin n),
          ∀ e a : Equiv.Perm (Fin n), c2Action e a →
            c2RepairDistance u v e a > c * c2DefectDistance u v)

end

end MathlibPlus.Open.ResearchBatch.D0125
