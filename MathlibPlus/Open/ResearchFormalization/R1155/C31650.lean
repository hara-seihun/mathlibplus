import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R1155C31650

noncomputable section

abbrev Boolean := ZMod 2

def linearityCondition {H : Type*} [AddCommGroup H]
    (b : H → Boolean) (h : H) : Prop :=
  ∀ u : H, b (h + u) = b h + b u

def linearitySet {H : Type*} [AddCommGroup H]
    (b : H → Boolean) : Set H :=
  {h | linearityCondition b h}

def linearitySubgroupWitness {H : Type*} [AddCommGroup H]
    (b : H → Boolean) (L : AddSubgroup H) : Prop :=
  ∀ h : H, h ∈ L ↔ h ∈ linearitySet b

def restrictionIsHom {H : Type*} [AddCommGroup H]
    (b : H → Boolean) (L : AddSubgroup H) : Prop :=
  ∀ x y : L, b (x.1 + y.1) = b x.1 + b y.1

def oddPartKilled {A : Type*} [AddCommGroup A]
    (χ : (A × (Boolean × Boolean)) →+ Boolean) : Prop :=
  ∀ a : A, χ (a, (0, 0)) = 0

def elementaryTwoSubspace {A : Type*} [AddCommGroup A]
    (L : AddSubgroup (A × (Boolean × Boolean)))
    (W : Submodule Boolean (Boolean × Boolean)) : Prop :=
  ∀ v : Boolean × Boolean,
    v ∈ W ↔ ((0, v) : A × (Boolean × Boolean)) ∈ L

def claim31650 : Prop :=
  (∀ (H : Type*) [AddCommGroup H]
      (b : H → Boolean),
      b 0 = 0 →
        ∃ L : AddSubgroup H,
          linearitySubgroupWitness b L ∧
            restrictionIsHom b L) ∧
    (∀ (A : Type*) [Fintype A] [AddCommGroup A],
      Odd (Fintype.card A) →
        let H := A × (Boolean × Boolean)
        ∀ b : H → Boolean,
          b 0 = 0 →
            ∃ L : AddSubgroup H,
              linearitySubgroupWitness b L ∧
                restrictionIsHom b L ∧
                  ∃ W : Submodule Boolean (Boolean × Boolean),
                    elementaryTwoSubspace L W ∧
                      ∃ χ : H →+ Boolean,
                        (∀ h : L, χ h.1 = b h.1) ∧
                          oddPartKilled χ)

end

end MathlibPlus.Open.ResearchFormalization.R1155C31650
