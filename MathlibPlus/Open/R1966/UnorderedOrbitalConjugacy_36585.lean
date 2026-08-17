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

private def distinctUnorderedPair (p : Sym2 V) : Prop :=
  ∃ x y : V, x ≠ y ∧ Sym2.mk x y = p

private def sameUnorderedOrbit
    (H : PermutationGroup) (p q : Sym2 V) : Prop :=
  ∃ h : H, Sym2.map h.1 p = q

private def unorderedOrbitalPreserver
    (H : PermutationGroup) (σ : Equiv.Perm V) : Prop :=
  ∀ p q : Sym2 V,
    distinctUnorderedPair p → distinctUnorderedPair q →
      (sameUnorderedOrbit H p q ↔
        sameUnorderedOrbit H p (Sym2.map σ q))

private def conjugateSubgroupsBy
    (σ : Equiv.Perm V) (R S : PermutationGroup) : Prop :=
  ∀ ρ : Equiv.Perm V,
    ρ ∈ S ↔ σ.symm * ρ * σ ∈ R

private def literalSubgroups :=
  {R : PermutationGroup // literalRegularE8 R}

/-- Claim 36585: every literal regular affine E8 pair is conjugate inside
its exact unordered-orbital color stabilizer. -/
def claim36585 : Prop :=
  ∀ (E F : literalSubgroups),
    ∃ σ : Equiv.Perm V,
      unorderedOrbitalPreserver (E.1 ⊔ F.1) σ ∧
        conjugateSubgroupsBy σ E.1 F.1

end MathlibPlus.Open.R1966
