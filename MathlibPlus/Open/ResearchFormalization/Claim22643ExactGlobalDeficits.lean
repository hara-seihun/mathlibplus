import Mathlib

open scoped BigOperators

noncomputable section

namespace MathlibPlus.Open.ResearchFormalization.Claim22643ExactGlobalDeficits

private abbrev Three := Fin 3

private def previous (i : Three) : Three :=
  Fin.ofNat 3 (i.1 + 2)

private def next (i : Three) : Three :=
  Fin.ofNat 3 (i.1 + 1)

private def nextTwo (i : Three) : Three :=
  next (next i)

private abbrev Family (α : Type*) := Finset (Finset α)

private def familyUnionClosed {α : Type*} [DecidableEq α]
    (family : Family α) : Prop :=
  ∀ ⦃S T : Finset α⦄, S ∈ family → T ∈ family → S ∪ T ∈ family

private def unionOf {α : Type*} [DecidableEq α]
    (sets : Finset (Finset α)) : Finset α :=
  sets.biUnion id

private def coordinateDeficit {α : Type*} [DecidableEq α]
    (family : Family α) (x : α) : ℤ :=
  ((family.filter (fun S => x ∉ S)).card : ℤ) -
    ((family.filter (fun S => x ∈ S)).card : ℤ)

private def codeOnBlock {α : Type*} [DecidableEq α]
    (block : Finset α) (code : Finset (Finset α)) : Prop :=
  code.Nonempty ∧
    (∀ S ∈ code, S.Nonempty ∧ S ⊆ block) ∧
      (∀ S ∈ code, ∀ T ∈ code, S ∪ T ∈ code) ∧
        block ∈ code

private structure SixCodeGrid (α : Type*) [DecidableEq α] where
  t : Three → α
  A : Three → Finset α
  C : Three → Finset α
  P : Three → Finset (Finset α)
  L : Three → Finset (Finset α)

private def gridValid {α : Type*} [DecidableEq α]
    (g : SixCodeGrid α) : Prop :=
  (∀ i : Three,
    (g.A i).Nonempty ∧ (g.C i).Nonempty ∧
      codeOnBlock (g.A i) (g.P i) ∧
        codeOnBlock (g.C i) (g.L i)) ∧
    (∀ i j : Three, i ≠ j →
      Disjoint (g.A i) (g.A j) ∧
        Disjoint (g.C i) (g.C j) ∧
          Disjoint (g.A i) (g.C j) ∧
            Disjoint (g.C i) (g.A j)) ∧
    (∀ i : Three, Disjoint (g.A i) (g.C i)) ∧
    Function.Injective g.t ∧
    (∀ i j : Three, ∀ x : α,
      (x ∈ g.A i ∨ x ∈ g.C i) → g.t j ≠ x)

private def sixCodeGenerators {α : Type*} [DecidableEq α]
    (g : SixCodeGrid α) : Finset (Finset α) :=
  Finset.univ.biUnion (fun i =>
    (g.P i).image (fun S => insert (g.t i) S) ∪
      {g.C i} ∪
        (g.L i).image (fun S => insert (g.t (next i)) S))

private def fullSixCodeFamily {α : Type*} [DecidableEq α]
    (g : SixCodeGrid α) : Family α :=
  (sixCodeGenerators g).powerset.image unionOf

private def sixCodeFamily {α : Type*} [DecidableEq α]
    (g : SixCodeGrid α) : Family α :=
  (fullSixCodeFamily g).erase ∅

private def channelGenerators {α : Type*} [DecidableEq α]
    (g : SixCodeGrid α) (i : Three) : Finset (Finset α) :=
  (g.P i).image (fun S => insert (g.t i) S) ∪
    {g.C i} ∪
      (g.L (previous i)).image (fun S => insert (g.t i) S)

private def channelFamily {α : Type*} [DecidableEq α]
    (g : SixCodeGrid α) (i : Three) : Family α :=
  (channelGenerators g i).powerset.image unionOf

private def channelWeight {α : Type*} [DecidableEq α]
    (g : SixCodeGrid α) (i : Three) : ℤ :=
  ((((g.P i).card + 1) * ((g.L (previous i)).card + 1) + 1 : ℕ) : ℤ)

private def codeDeficit {α : Type*} [DecidableEq α]
    (code : Finset (Finset α)) (x : α) : ℤ :=
  ((code.filter (fun S => x ∉ S)).card : ℤ) -
    ((code.filter (fun S => x ∈ S)).card : ℤ)

private def predecessorSignedWeight {α : Type*} [DecidableEq α]
    (g : SixCodeGrid α) (i : Three) (x : α) : ℤ :=
  ((g.L (previous i)).card : ℤ) + 2 +
    (((g.L (previous i)).card : ℤ) + 1) * codeDeficit (g.P i) x

private def optionalSignedWeight {α : Type*} [DecidableEq α]
    (g : SixCodeGrid α) (i : Three) (x : α) : ℤ :=
  ((g.P (next i)).card : ℤ) +
    (((g.P (next i)).card : ℤ) + 1) * codeDeficit (g.L i) x

private def productRepresentationUnique {α : Type*} [DecidableEq α]
    (g : SixCodeGrid α) : Prop :=
  (∀ states : Three → Finset α,
    (∀ i : Three, states i ∈ channelFamily g i) →
      unionOf (Finset.univ.image states) ∈ fullSixCodeFamily g) ∧
    (∀ S ∈ fullSixCodeFamily g,
      ∃! states : Three → Finset α,
        (∀ i : Three, states i ∈ channelFamily g i) ∧
          S = unionOf (Finset.univ.image states))

/-- Claim 22643: the three disjoint channels have a unique Cartesian product
representation, and deletion of the sole global empty member subtracts one
from every coordinate deficit.  The two displayed formulas are the complete
signed global deficits; their cross-channel factors are positive state counts
and there is no mixed signed term. -/
def claim22643 : Prop :=
  ∀ {α : Type*} [DecidableEq α] (g : SixCodeGrid α),
    gridValid g →
      productRepresentationUnique g ∧
        (∅ : Finset α) ∈ fullSixCodeFamily g ∧
        (∀ x : α,
          coordinateDeficit (sixCodeFamily g) x =
            coordinateDeficit (fullSixCodeFamily g) x - 1) ∧
        (∀ i : Three, 0 < channelWeight g i) ∧
        (∀ i : Three, ∀ x ∈ g.A i,
          coordinateDeficit (sixCodeFamily g) x =
            predecessorSignedWeight g i x *
                channelWeight g (next i) * channelWeight g (nextTwo i) - 1) ∧
        (∀ i : Three, ∀ x ∈ g.C i,
          coordinateDeficit (sixCodeFamily g) x =
            optionalSignedWeight g i x *
                channelWeight g (nextTwo i) * channelWeight g i - 1)

end MathlibPlus.Open.ResearchFormalization.Claim22643ExactGlobalDeficits
