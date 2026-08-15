import Mathlib

namespace MathlibPlus.Open.FormalizationBatch.AffineGroups

private abbrev V (p : ℕ) := ZMod p × ZMod p

private def affineGroupConclusion
    (p : ℕ) (t1 t2 q1 q2 : Equiv.Perm (V p)) : Prop :=
  let P : Subgroup (Equiv.Perm (V p)) :=
    Subgroup.closure ({t1, t2} : Set (Equiv.Perm (V p)))
  let Q : Subgroup (Equiv.Perm (V p)) :=
    Subgroup.closure ({q1, q2} : Set (Equiv.Perm (V p)))
  let generated : Subgroup (Equiv.Perm (V p)) :=
    Subgroup.closure ((P : Set (Equiv.Perm (V p))) ∪
      (Q : Set (Equiv.Perm (V p))))
  (∀ u v : V p, ∃! σ : P, (σ : Equiv.Perm (V p)) u = v) ∧
    (∀ u v : V p, ∃! σ : Q, (σ : Equiv.Perm (V p)) u = v) ∧
    (∀ σ τ : P, σ * τ = τ * σ) ∧
    (∀ σ : P, σ ^ p = 1) ∧
    (∀ σ τ : Q, σ * τ = τ * σ) ∧
    (∀ σ : Q, σ ^ p = 1) ∧
    Nat.card P = p ^ 2 ∧
    Nat.card Q = p ^ 2 ∧
    P ≠ Q ∧
    P ⊓ Q = Subgroup.closure ({t2} : Set (Equiv.Perm (V p))) ∧
    Nat.card (↥(P ⊓ Q)) = p ∧
    (∀ σ : Equiv.Perm (V p),
      σ ∈ generated ↔
        ∃ a b c : ZMod p, ∀ x y : ZMod p,
          σ (x, y) = (x + a, y + c * x + b)) ∧
    Nat.card generated = p ^ 3

/-- The four explicit affine transformations and the generated subgroups. -/
def explicitAffineTransformations
    (p : ℕ) (hp : Nat.Prime p) (hodd : Odd p) : Prop :=
  ∃ t1 t2 q1 q2 : Equiv.Perm (V p),
    (∀ x y : ZMod p, t1 (x, y) = (x + 1, y)) ∧
      (∀ x y : ZMod p, t2 (x, y) = (x, y + 1)) ∧
      (∀ x y : ZMod p, q1 (x, y) = (x + 1, y + x)) ∧
      (∀ x y : ZMod p, q2 (x, y) = (x, y + 1)) ∧
      ∃ P Q : Subgroup (Equiv.Perm (V p)),
        P = Subgroup.closure ({t1, t2} : Set (Equiv.Perm (V p))) ∧
          Q = Subgroup.closure ({q1, q2} : Set (Equiv.Perm (V p)))

/-- The generated affine group and its common kernel intersection. -/
def generatedAffineGroupAndKernelIntersection
    (p : ℕ) (hp : Nat.Prime p) (hodd : Odd p) : Prop :=
  ∀ t1 t2 q1 q2 : Equiv.Perm (V p),
    ((∀ x y : ZMod p, t1 (x, y) = (x + 1, y)) ∧
      (∀ x y : ZMod p, t2 (x, y) = (x, y + 1)) ∧
      (∀ x y : ZMod p, q1 (x, y) = (x + 1, y + x)) ∧
      (∀ x y : ZMod p, q2 (x, y) = (x, y + 1))) →
      affineGroupConclusion p t1 t2 q1 q2

/-- Independent alignment of the duplicate admitted statement. -/
def generatedAffineGroupAndKernelIntersectionDuplicate
    (p : ℕ) (hp : Nat.Prime p) (hodd : Odd p) : Prop :=
  ∀ t1 t2 q1 q2 : Equiv.Perm (V p),
    ((∀ x y : ZMod p, t1 (x, y) = (x + 1, y)) ∧
      (∀ x y : ZMod p, t2 (x, y) = (x, y + 1)) ∧
      (∀ x y : ZMod p, q1 (x, y) = (x + 1, y + x)) ∧
      (∀ x y : ZMod p, q2 (x, y) = (x, y + 1))) →
      affineGroupConclusion p t1 t2 q1 q2

end MathlibPlus.Open.FormalizationBatch.AffineGroups
