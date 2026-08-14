import Mathlib

namespace MathlibPlus.Open.ResearchFormalization

/-- Identity-free inverse-closed connection sets in an additive group. -/
def additiveIdentityFree {G : Type*} [Zero G] (S : Set G) : Prop :=
  ∀ x : G, x ∈ S → x ≠ 0

def additiveInverseClosed {G : Type*} [Neg G] (S : Set G) : Prop :=
  ∀ x : G, x ∈ S → -x ∈ S

def additiveSpanning {G : Type*} [AddGroup G] (S : Set G) : Prop :=
  AddSubgroup.closure S = ⊤

def additiveCayleyIsomorphism {G : Type*} [Sub G] (S T : Set G) (q : G → G) : Prop :=
  ∀ x y : G, y - x ∈ S ↔ q y - q x ∈ T

/-- Exact finite low-side census data for the same connection-set carrier. -/
noncomputable def lowValencyCensus59310
    {G : Type*} [Fintype G] [AddCommGroup G] : Prop := by
  classical
  let C := {S : Finset G //
    S.card ≤ 18 ∧ 0 ∉ S ∧ (∀ x : G, x ∈ S → -x ∈ S)}
  let addRel : C → C → Prop := fun A B =>
    ∃ α : G ≃+ G,
      Set.image (α : G → G) (A.1 : Set G) = (B.1 : Set G)
  let graphRel : C → C → Prop := fun A B =>
    ∃ e : G ≃ G, ∀ x y : G,
      (y - x ∈ (A.1 : Set G) ↔ e y - e x ∈ (B.1 : Set G))
  let addSetoid : Setoid C :=
    { r := Relation.EqvGen addRel
      iseqv :=
        { refl := fun x => Relation.EqvGen.refl x
          symm := fun {a b} h => Relation.EqvGen.symm a b h
          trans := fun {a b c} h₁ h₂ => Relation.EqvGen.trans a b c h₁ h₂ } }
  let graphSetoid : Setoid C :=
    { r := Relation.EqvGen graphRel
      iseqv :=
        { refl := fun x => Relation.EqvGen.refl x
          symm := fun {a b} h => Relation.EqvGen.symm a b h
          trans := fun {a b c} h₁ h₂ => Relation.EqvGen.trans a b c h₁ h₂ } }
  letI : Fintype C := Fintype.ofFinite C
  exact Fintype.card C = 31621024 ∧
    Fintype.card (Quotient addSetoid) = 228516 ∧
    Fintype.card (Quotient graphSetoid) = 228516 ∧
    (∀ A B : C, Relation.EqvGen graphRel A B →
      Relation.EqvGen addRel A B)

/-- The low/high-valency ordinary-CI assertion on `(C_3)^2 × C_7`, together
    with the exact low-side census and singleton-fibre assertion. -/
def claim59310 : Prop :=
  let G := (Fin 2 → ZMod 3) × ZMod 7
  (∀ (S T : Set G),
    additiveIdentityFree S ∧ additiveIdentityFree T ∧
    additiveInverseClosed S ∧ additiveInverseClosed T ∧
    ((S.ncard ≤ 18 ∧ T.ncard ≤ 18) ∨
      (44 ≤ S.ncard ∧ 44 ≤ T.ncard)) →
    ∀ (q : G → G),
      Function.Bijective q →
      additiveCayleyIsomorphism S T q →
      ∃ α : G ≃+ G, Set.image (α : G → G) S = T) ∧
  lowValencyCensus59310 (G := G)

end MathlibPlus.Open.ResearchFormalization
