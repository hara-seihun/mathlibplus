import Mathlib
import MathlibPlus.Open.GroupTheory.RegularBlockSubgroups

namespace MathlibPlus.Open.ResearchFormalization.R1155C31648

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

def autPerm {Ω : Type*} {Aut : Subgroup (Perm Ω)} (a : Aut) : Perm Ω :=
  a

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

def actualBlockAction {Ω : Type*} {B : Finset (Set Ω)}
    (Aut : Subgroup (Perm Ω))
    (π : Aut →* Perm (BlockType B)) : Prop :=
  ∀ a : Aut, ∀ U : BlockType B,
    ((π a) U).1 = (a : Perm Ω) '' U.1

def preservesBlocks {Ω : Type*} {B : Finset (Set Ω)}
    {Aut : Subgroup (Perm Ω)} (R : Subgroup Aut) : Prop :=
  ∀ r : R, ∀ U : BlockType B, copyPerm r '' U.1 ∈ B

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

def conjugatesInAut {Ω : Type*}
    {Aut : Subgroup (Perm Ω)} {R T : Subgroup Aut}
    (f : Aut) : Prop :=
  (∀ t : T, ∃ r : R,
    copyPerm t = autPerm f * copyPerm r * (autPerm f)⁻¹) ∧
    ∀ r : R, ∃ t : T,
      copyPerm r = (autPerm f)⁻¹ * copyPerm t * autPerm f

def sectionFiber {A : Type*} (h : QuotientGroup A) :
    Set (QuotientGroup A × ZMod 2) :=
  {(h, (0 : ZMod 2)), (h, (1 : ZMod 2))}

def sectionCoordinates {A Ω : Type*}
    (B : Finset (Set Ω))
    (coord : Ω ≃ (QuotientGroup A × ZMod 2)) : Prop :=
  (∀ U : BlockType B, ∃ h : QuotientGroup A,
    coord '' U.1 = sectionFiber h) ∧
    ∀ h : QuotientGroup A, ∃ U : BlockType B,
      coord '' U.1 = sectionFiber h

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
        (∀ g : BaseGroup A,
          π (eR g).1 = (eQ (quotientMap q g) : Perm (BlockType B))) ∧
          ∀ g : BaseGroup A,
            π (eT g).1 = (eQ (quotientMap q g) : Perm (BlockType B))

def commonConfiguration {A Ω : Type*}
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

def normalizedRelabeling {A Ω : Type*}
    [CommGroup A] {B : Finset (Set Ω)}
    {Aut : Subgroup (Perm Ω)} {R T : Subgroup Aut}
    {Q : Subgroup (Perm (BlockType B))}
    (Γ : Ω → Ω → Prop) (π : Aut →* Perm (BlockType B))
    (eQ : QuotientGroup A ≃* Q)
    (o : Ω) (f : Aut) : Prop :=
  relationAutomorphism Γ (autPerm f) ∧
    autPerm f o = o ∧
      (conjugatesInAut (R := R) (T := T) f) ∧
        ∀ h : QuotientGroup A,
          π f * (eQ h : Perm (BlockType B)) * (π f)⁻¹ =
            (eQ h : Perm (BlockType B))

def claim31648 : Prop :=
  ∀ {A Ω : Type*} [Fintype A] [CommGroup A] [Fintype Ω]
    (Γ : Ω → Ω → Prop) (Aut : Subgroup (Perm Ω))
    (B : Finset (Set Ω)) (R T : Subgroup Aut)
    (π : Aut →* Perm (BlockType B))
    (Q : Subgroup (Perm (BlockType B)))
    (eR : BaseGroup A ≃* R) (eT : BaseGroup A ≃* T)
    (eQ : QuotientGroup A ≃* Q)
    (q : Q8 →* V4) (o : Ω)
    (coord : Ω ≃ (QuotientGroup A × ZMod 2)),
    commonConfiguration Γ Aut B R T π Q eR eT eQ q →
      MathlibPlus.Open.finiteBlockSystem B →
        twoPointSystem B →
          sectionCoordinates B coord →
            coord o = ((1 : QuotientGroup A), (0 : ZMod 2)) →
              ∀ f : Aut,
                normalizedRelabeling (R := R) (T := T) (Q := Q) Γ π eQ o f →
                  ∃ b : QuotientGroup A → ZMod 2,
                    b 1 = 0 ∧
                      (∀ U : BlockType B,
                        (autPerm f) '' U.1 = U.1) ∧
                        ∀ h : QuotientGroup A, ∀ e : ZMod 2,
                          coord (autPerm f (coord.symm (h, e))) =
                            (h, e + b h)

end

end MathlibPlus.Open.ResearchFormalization.R1155C31648
