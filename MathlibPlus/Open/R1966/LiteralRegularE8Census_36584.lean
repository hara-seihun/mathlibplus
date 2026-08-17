import Mathlib

namespace MathlibPlus.Open.R1966

private abbrev F2 := ZMod 2
private abbrev V := Fin 3 → F2
private abbrev PermutationGroup := Subgroup (Equiv.Perm V)

private def affinePermutation (σ : Equiv.Perm V) : Prop :=
  ∃ A : V ≃ₗ[F2] V, ∃ b : V,
    ∀ x : V, σ x = A x + b

private def regularSubgroup (R : PermutationGroup) : Prop :=
  ∀ x y : V, ∃! r : R, r.1 x = y

private def literalRegularE8 (R : PermutationGroup) : Prop :=
  (∀ r : R, affinePermutation r.1) ∧
    regularSubgroup R ∧
    Nat.card R = 8 ∧
    (∀ a b : R, a * b = b * a) ∧
    (∀ a : R, a ^ 2 = 1) ∧
    Nonempty (R ≃* Multiplicative V)

private def literalRegularE8Subgroups :=
  {R : PermutationGroup // literalRegularE8 R}

/-- Claim 36584: the literal affine, regular elementary-abelian subgroup
carrier in `AGL(3,2)` has exactly eight members and 64 ordered pairs. -/
def claim36584 : Prop :=
  Nat.card literalRegularE8Subgroups = 8 ∧
    Nat.card (literalRegularE8Subgroups × literalRegularE8Subgroups) = 64

end MathlibPlus.Open.R1966
