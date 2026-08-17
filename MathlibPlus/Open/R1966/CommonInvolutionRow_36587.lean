import Mathlib

namespace MathlibPlus.Open.R1966

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
  (∀ r : R, affinePermutation r.1) ∧ regularSubgroup R ∧
    Nat.card R = 8 ∧ (∀ a b : R, a * b = b * a) ∧
    (∀ a : R, a ^ 2 = 1) ∧ Nonempty (R ≃* Multiplicative V)

private def literalSubgroups :=
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

private def subgroupCard (H : PermutationGroup) : ℕ := Nat.card H

private def conjugateInGenerated
    (R S : PermutationGroup) : Prop :=
  ∃ σ : {σ : Equiv.Perm V // σ ∈ R ⊔ S},
    conjugateSubgroupsBy σ.1 R S

private def rowOne (E F : literalSubgroups) : Prop :=
  let H := E.1 ⊔ F.1
  subgroupCard H = 8 ∧ subgroupCard (E.1 ⊓ F.1) = 8 ∧
    numberOfUnorderedOrbitals H = 7 ∧ closureOrder H = 8 ∧
    conjugateInGenerated E.1 F.1

private def rowTwo (E F : literalSubgroups) : Prop :=
  let H := E.1 ⊔ F.1
  subgroupCard H = 32 ∧ subgroupCard (E.1 ⊓ F.1) = 2 ∧
    numberOfUnorderedOrbitals H = 4 ∧ closureOrder H = 64 ∧
    ¬ conjugateInGenerated E.1 F.1

private def rowThree (E F : literalSubgroups) : Prop :=
  let H := E.1 ⊔ F.1
  subgroupCard H = 96 ∧ subgroupCard (E.1 ⊓ F.1) = 1 ∧
    numberOfUnorderedOrbitals H = 2 ∧ closureOrder H = 1152 ∧
    conjugateInGenerated E.1 F.1

private def exactlyOneRow (E F : literalSubgroups) : Prop :=
  (rowOne E F ∨ rowTwo E F ∨ rowThree E F) ∧
    ¬(rowOne E F ∧ rowTwo E F) ∧
    ¬(rowOne E F ∧ rowThree E F) ∧
    ¬(rowTwo E F ∧ rowThree E F)


/-- Claim 36587: the unique generated-group nonconjugacy row is the
order-32 row, and its intersection supplies one literal common involution. -/
def claim36587 : Prop :=
  Nat.card (literalSubgroups × literalSubgroups) = 64 ∧
    Nat.card {p : literalSubgroups × literalSubgroups //
      rowTwo p.1 p.2} = 14 ∧
    (∀ E F : literalSubgroups,
      ¬ conjugateInGenerated E.1 F.1 → rowTwo E F) ∧
    (∀ E F : literalSubgroups, rowTwo E F →
      ∃ z : Equiv.Perm V,
        z ∈ E.1 ∧ z ∈ F.1 ∧ z ≠ 1 ∧ z ^ 2 = 1 ∧
        (∀ w : Equiv.Perm V,
          w ∈ E.1 → w ∈ F.1 → w ≠ 1 → w = z))

end

end MathlibPlus.Open.R1966
