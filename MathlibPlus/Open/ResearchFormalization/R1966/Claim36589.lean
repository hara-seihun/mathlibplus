import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R1966.Claim36589

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

private abbrev literalSubgroups :=
  {R : PermutationGroup // literalRegularE8 R}

private def distinctUnorderedPair (p : Sym2 V) : Prop :=
  ∃ x y : V, x ≠ y ∧ Sym2.mk x y = p

private def sameUnorderedOrbit
    (H : PermutationGroup) (p q : Sym2 V) : Prop :=
  ∃ h : H, Sym2.map h.1 p = q

private def orbitalSet (H : PermutationGroup)
    (p : {q : Sym2 V // distinctUnorderedPair q}) : Set (Sym2 V) :=
  {q | distinctUnorderedPair q ∧ sameUnorderedOrbit H p.1 q}

private def numberOfUnorderedOrbitals (H : PermutationGroup) : ℕ :=
  Set.ncard (Set.range (orbitalSet H))

private def unorderedOrbitalPreserver
    (H : PermutationGroup) (σ : Equiv.Perm V) : Prop :=
  ∀ p q : Sym2 V,
    distinctUnorderedPair p → distinctUnorderedPair q →
      (sameUnorderedOrbit H p q ↔
        sameUnorderedOrbit H p (Sym2.map σ q))

private def closureOrder (H : PermutationGroup) : ℕ :=
  Nat.card {σ : Equiv.Perm V // unorderedOrbitalPreserver H σ}

private def conjugateSubgroupsBy
    (σ : Equiv.Perm V) (R S : PermutationGroup) : Prop :=
  ∀ ρ : Equiv.Perm V,
    ρ ∈ S ↔ σ.symm * ρ * σ ∈ R

private def conjugateInGenerated
    (R S : PermutationGroup) : Prop :=
  ∃ σ : {σ : Equiv.Perm V // σ ∈ R ⊔ S},
    conjugateSubgroupsBy σ.1 R S

private def subgroupCard (H : PermutationGroup) : ℕ :=
  Nat.card H

private def equalPairData (E F : literalSubgroups) : Prop :=
  E.1 = F.1 ∧
    E.1 ⊔ F.1 = E.1 ∧
    subgroupCard (E.1 ⊔ F.1) = 8 ∧
    subgroupCard (E.1 ⊓ F.1) = 8 ∧
    numberOfUnorderedOrbitals (E.1 ⊔ F.1) = 7 ∧
    closureOrder (E.1 ⊔ F.1) = 8 ∧
    conjugateInGenerated E.1 F.1

/-- Claim 36589: the diagonal ordered pairs of literal regular affine
`C₂^3` subgroups are exactly the eight equal pairs, and each has generated
and intersection order eight, seven unordered orbitals, closure order eight,
and conjugacy inside the generated group. -/
def claim36589 : Prop :=
  Nat.card {p : literalSubgroups × literalSubgroups // p.1 = p.2} = 8 ∧
    ∀ E F : literalSubgroups, E = F → equalPairData E F

end

end MathlibPlus.Open.ResearchFormalization.R1966.Claim36589
