import Mathlib

noncomputable section
open scoped BigOperators
open Set

namespace MathlibPlus.Open.Order72Batch

abbrev order72Group := (ZMod 2 × ZMod 2 × ZMod 2) × (ZMod 3 × ZMod 3)

instance : Fintype order72Group := inferInstance

abbrev connection18 :=
  {S : Finset order72Group //
    0 ∉ S ∧ S.card = 18 ∧ ∀ x ∈ S, -x ∈ S}

def cayleyGraph (S : connection18) : SimpleGraph order72Group :=
  SimpleGraph.fromRel (fun x y => y - x ∈ S.1)

def connectionComplement (S : connection18) : Finset order72Group :=
  (Finset.univ.erase 0) \ S.1

def samePresentationOrbit (S T : connection18) : Prop :=
  ∃ α : order72Group ≃+ order72Group, S.1.image α = T.1

def exactConnectionSpaceCount : Prop := by
  classical
  letI := Fintype.ofFinite connection18
  exact Fintype.card connection18 = 373081404

def exactOrbitRepresentativeCount : Prop :=
  ∃ R : Finset connection18,
    R.card = 112940 ∧
      ∀ S : connection18, ∃! r : connection18, r ∈ R ∧ samePresentationOrbit S r

def exactGraphTypeRepresentativeCount : Prop :=
  ∃ R : Finset connection18,
    R.card = 112940 ∧
      ∀ S : connection18, ∃! r : connection18, r ∈ R ∧
        Nonempty (SimpleGraph.Iso (cayleyGraph S) (cayleyGraph r))

def exactCompleteOrbitAndGraphCounts : Prop :=
  exactConnectionSpaceCount ∧
    exactOrbitRepresentativeCount ∧
    exactGraphTypeRepresentativeCount

def exactValency18Scope : Prop :=
  Fintype.card order72Group = 72 ∧
    (∀ S : connection18, (connectionComplement S).card = 53) ∧
    exactCompleteOrbitAndGraphCounts

def graphAutomorphism (S : connection18) (φ : Equiv.Perm order72Group) : Prop :=
  ∀ x y : order72Group,
    (cayleyGraph S).Adj x y ↔ (cayleyGraph S).Adj (φ x) (φ y)

def regularPermutationSubgroup (H : Subgroup (Equiv.Perm order72Group)) : Prop :=
  ∀ x y : order72Group, ∃! h : H, (h : Equiv.Perm order72Group) x = y

def naturalRegularCopy : Subgroup (Equiv.Perm order72Group) :=
  Subgroup.closure (Set.range (fun g : order72Group => Equiv.addRight g))

def conjugatesToNaturalCopy (H : Subgroup (Equiv.Perm order72Group))
    (φ : Equiv.Perm order72Group) : Prop :=
  ∀ h : Equiv.Perm order72Group,
    h ∈ H ↔ φ⁻¹ * h * φ ∈ naturalRegularCopy

def valency18CI : Prop :=
  ∀ S : connection18,
    ∀ H : Subgroup (Equiv.Perm order72Group),
      regularPermutationSubgroup H →
      Nonempty (H ≃* Multiplicative order72Group) →
      (∀ h : Equiv.Perm order72Group, h ∈ H → graphAutomorphism S h) →
      ∃ φ : Equiv.Perm order72Group,
        graphAutomorphism S φ ∧ conjugatesToNaturalCopy H φ

end MathlibPlus.Open.Order72Batch
