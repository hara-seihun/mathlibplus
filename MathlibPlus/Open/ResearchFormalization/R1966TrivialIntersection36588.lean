import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R1966TrivialIntersection36588

noncomputable section

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

private def orbitalPreserver
    (H : PermutationGroup) (σ : Equiv.Perm V) : Prop :=
  ∀ p q : Sym2 V,
    distinctUnorderedPair p → distinctUnorderedPair q →
      (sameUnorderedOrbit H p q ↔
        sameUnorderedOrbit H p (Sym2.map σ q))

private def literalSubgroups :=
  {R : PermutationGroup // literalRegularE8 R}

private def subgroupCard (H : PermutationGroup) : ℕ := Nat.card H

private def numberOfUnorderedOrbitals (H : PermutationGroup) : ℕ :=
  Set.ncard (Set.range (fun p : {q : Sym2 V // distinctUnorderedPair q} =>
    {q : Sym2 V | distinctUnorderedPair q ∧ sameUnorderedOrbit H p.1 q}))

private def orbitalClosureOrder (H : PermutationGroup) : ℕ :=
  Nat.card {σ : Equiv.Perm V // orbitalPreserver H σ}

private def conjugateInGenerated
    (R S : PermutationGroup) : Prop :=
  ∃ σ : {σ : Equiv.Perm V // σ ∈ R ⊔ S},
    ∀ ρ : Equiv.Perm V,
      (ρ ∈ S ↔ σ.1.symm * ρ * σ.1 ∈ R)

/-- Claim 36588: every one of the exactly forty-two trivial-intersection
ordered literal affine E8 pairs has the row-three orders, two unordered
orbitals, closure order 1152, and conjugacy inside its generated group. -/
def claim36588 : Prop :=
  Nat.card {p : literalSubgroups × literalSubgroups //
      subgroupCard (p.1.1 ⊓ p.2.1) = 1} = 42 ∧
    ∀ E F : literalSubgroups,
      subgroupCard (E.1 ⊓ F.1) = 1 →
        subgroupCard (E.1 ⊔ F.1) = 96 ∧
          numberOfUnorderedOrbitals (E.1 ⊔ F.1) = 2 ∧
          orbitalClosureOrder (E.1 ⊔ F.1) = 1152 ∧
          conjugateInGenerated E.1 F.1

end

end MathlibPlus.Open.ResearchFormalization.R1966TrivialIntersection36588
