import Mathlib
import MathlibPlus.Open.GroupTheory.RegularBlockSubgroups

namespace MathlibPlus.Open.ResearchFormalization.R1155C31646

noncomputable section

abbrev Perm (Ω : Type*) := Equiv.Perm Ω
abbrev Q8 := QuaternionGroup 2
abbrev V4 := Multiplicative (Fin 2 → ZMod 2)
abbrev BaseGroup (A : Type*) := A × Q8
abbrev QuotientGroup (A : Type*) := A × V4
abbrev BlockType {Ω : Type*} (B : Finset (Set Ω)) :=
  MathlibPlus.Open.blockType B

def quotientMap {A : Type*} [CommGroup A]
    (q : Q8 →* V4) : BaseGroup A →* QuotientGroup A :=
  MonoidHom.prod (MonoidHom.fst A Q8) (q.comp (MonoidHom.snd A Q8))

def quotientProjectionData (q : Q8 →* V4) : Prop :=
  Function.Surjective q ∧
    ∀ x : Q8,
      q x = 1 ↔ x ∈ (Subgroup.center Q8 : Set Q8)

def relationAutomorphism {Ω : Type*}
    (Γ : Ω → Ω → Prop) (p : Perm Ω) : Prop :=
  ∀ x y : Ω, Γ (p x) (p y) ↔ Γ x y

def fullRelationAutomorphismGroup {Ω : Type*}
    (Γ : Ω → Ω → Prop) (Aut : Subgroup (Perm Ω)) : Prop :=
  ∀ p : Perm Ω, p ∈ Aut ↔ relationAutomorphism Γ p

def twoPointSystem {Ω : Type*} (B : Finset (Set Ω)) : Prop :=
  ∀ U : BlockType B, U.1.ncard = 2

def copyPerm {Ω : Type*} {Aut : Subgroup (Perm Ω)}
    {R : Subgroup Aut} (r : R) : Perm Ω :=
  (r.1 : Aut)

def regularCopyOnOmega {A Ω : Type*}
    [Group A] [Fintype A] [Fintype Ω]
    {Aut : Subgroup (Perm Ω)} (R : Subgroup Aut)
    (e : A ≃* R) : Prop :=
  ∀ x y : Ω, ∃! a : A, copyPerm (e a) x = y

def regularCopyOnBlocks {A X : Type*}
    [Group A] [Fintype A] [Fintype X]
    (R : Subgroup (Perm X)) (e : A ≃* R) : Prop :=
  ∀ x y : X, ∃! a : A, ((e a : R) : Perm X) x = y

def preservesBlocks {Ω : Type*} {B : Finset (Set Ω)}
    {Aut : Subgroup (Perm Ω)} (R : Subgroup Aut) : Prop :=
  ∀ r : R, ∀ U : BlockType B, copyPerm r '' U.1 ∈ B

def actualBlockAction {Ω : Type*} {B : Finset (Set Ω)}
    (Aut : Subgroup (Perm Ω))
    (π : Aut →* Perm (BlockType B)) : Prop :=
  ∀ a : Aut, ∀ U : BlockType B,
    ((π a) U).1 = (a : Perm Ω) '' U.1

def sharedCentralSwap {A Ω : Type*}
    [CommGroup A] {B : Finset (Set Ω)}
    {Aut : Subgroup (Perm Ω)}
    {R T : Subgroup Aut}
    (eR : BaseGroup A ≃* R) (eT : BaseGroup A ≃* T) : Prop :=
  let z : BaseGroup A := (1, QuaternionGroup.a 2)
  copyPerm (eR z) = copyPerm (eT z) ∧
    ∀ U : BlockType B,
      copyPerm (eR z) '' U.1 = U.1 ∧
        ∀ x : Ω, x ∈ U.1 → copyPerm (eR z) x ≠ x

def oddHallFactorSplits {A : Type*} [CommGroup A] : Prop :=
  ∀ α : BaseGroup A ≃* BaseGroup A,
    ∃ αA : A ≃* A, ∃ αQ : Q8 ≃* Q8,
      ∀ a : A, ∀ q : Q8,
        α (a, q) = (αA a, αQ q)

def quaternionAutomorphismLifts (q : Q8 →* V4) : Prop :=
  ∀ α : V4 ≃* V4,
    ∃ β : Q8 ≃* Q8,
      ∀ x : Q8, q (β x) = α (q x)

def quotientAutomorphismLifts {A : Type*} [CommGroup A]
    (q : Q8 →* V4) : Prop :=
  ∀ α : QuotientGroup A ≃* QuotientGroup A,
    ∃ β : BaseGroup A ≃* BaseGroup A,
      ∀ g : BaseGroup A,
        quotientMap q (β g) = α (quotientMap q g)

def alignedQuotientData {A Ω : Type*}
    [Fintype A] [CommGroup A] [Fintype Ω]
    {B : Finset (Set Ω)} {Aut : Subgroup (Perm Ω)}
    {R T : Subgroup Aut}
    (π : Aut →* Perm (BlockType B))
    (Q : Subgroup (Perm (BlockType B)))
    (eR : BaseGroup A ≃* R) (eT : BaseGroup A ≃* T)
    (eQ : QuotientGroup A ≃* Q)
    (q : Q8 →* V4) : Prop :=
  R.map π = Q ∧
    T.map π = Q ∧
      regularCopyOnBlocks (A := QuotientGroup A) (X := BlockType B) Q eQ ∧
        ∀ g : BaseGroup A,
          π (eR g).1 = (eQ (quotientMap q g) : Perm (BlockType B)) ∧
            π (eT g).1 = (eQ (quotientMap q g) : Perm (BlockType B))

def commonAlignedConfiguration {A Ω : Type*}
    [Fintype A] [CommGroup A] [Fintype Ω]
    (Γ : Ω → Ω → Prop) (Aut : Subgroup (Perm Ω))
    (B : Finset (Set Ω)) (R T : Subgroup Aut)
    (π : Aut →* Perm (BlockType B))
    (Q : Subgroup (Perm (BlockType B)))
    (eR : BaseGroup A ≃* R) (eT : BaseGroup A ≃* T)
    (eQ : QuotientGroup A ≃* Q)
    (q : Q8 →* V4) : Prop :=
  Odd (Fintype.card A) ∧
    fullRelationAutomorphismGroup Γ Aut ∧
      MathlibPlus.Open.finiteBlockSystem B ∧
        twoPointSystem B ∧
          actualBlockAction Aut π ∧
            regularCopyOnOmega (A := BaseGroup A) (Ω := Ω) R eR ∧
              regularCopyOnOmega (A := BaseGroup A) (Ω := Ω) T eT ∧
                preservesBlocks (B := B) R ∧
                  preservesBlocks (B := B) T ∧
                    sharedCentralSwap (B := B) eR eT ∧
                      quotientProjectionData q ∧
                        alignedQuotientData π Q eR eT eQ q

def claim31646 : Prop :=
  (∀ (A : Type*) [Fintype A] [CommGroup A],
      Odd (Fintype.card A) →
        oddHallFactorSplits (A := A) ∧
          ∀ q : Q8 →* V4,
            quotientProjectionData q →
              quaternionAutomorphismLifts q ∧
                quotientAutomorphismLifts (A := A) q) ∧
    (∀ {A Ω : Type*} [Fintype A] [CommGroup A] [Fintype Ω]
      (Γ : Ω → Ω → Prop) (Aut : Subgroup (Perm Ω))
      (B : Finset (Set Ω)) (R T : Subgroup Aut)
      (π : Aut →* Perm (BlockType B))
      (Q : Subgroup (Perm (BlockType B)))
      (eR : BaseGroup A ≃* R) (eT : BaseGroup A ≃* T)
      (eQ : QuotientGroup A ≃* Q)
      (q : Q8 →* V4),
      commonAlignedConfiguration Γ Aut B R T π Q eR eT eQ q →
        ∃ θ : R ≃* T,
          let z : BaseGroup A := (1, QuaternionGroup.a 2)
          θ (eR z) = eT z ∧
            ∀ r : R,
              π (θ r).1 = π r.1)

end

end MathlibPlus.Open.ResearchFormalization.R1155C31646
