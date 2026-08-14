import Mathlib

namespace MathlibPlus.Open.Q60Batch

universe u

structure Q60 where
  i : ZMod 30
  e : Bool
  deriving DecidableEq, Fintype, Repr

def qmul : Q60 → Q60 → Q60
  | ⟨i, e⟩, ⟨j, f⟩ =>
      ⟨i + (if e then -j else j) +
          (if e then if f then (15 : ZMod 30) else 0 else 0),
       xor e f⟩

def qinv : Q60 → Q60
  | ⟨i, false⟩ => ⟨-i, false⟩
  | ⟨i, true⟩ => ⟨i + 15, true⟩

def qpow : Nat → Q60 → Q60
  | 0, _ => ⟨0, false⟩
  | n + 1, x => qmul (qpow n x) x

instance : Group Q60 where
  mul := qmul
  one := ⟨0, false⟩
  inv := qinv
  npow := qpow
  mul_assoc := by native_decide
  one_mul := by native_decide
  mul_one := by native_decide
  npow_zero := by intros; rfl
  npow_succ := by intros; rfl
  inv_mul_cancel := by native_decide

def qa : Q60 := ⟨1, false⟩
def qb : Q60 := ⟨0, true⟩

def PresentsQ60 (G : Type u) [Group G] (a b : G) : Prop :=
  a ^ 30 = 1 ∧
  b ^ 2 = a ^ 15 ∧
  b⁻¹ * a * b = a⁻¹ ∧
  ∀ (H : Type u) [Group H] (x y : H),
    x ^ 30 = 1 →
    y ^ 2 = x ^ 15 →
    y⁻¹ * x * y = x⁻¹ →
    ∃! f : G →* H, f a = x ∧ f b = y

def claim25589 : Prop :=
  PresentsQ60 Q60 qa qb ∧ Fintype.card Q60 = 60

noncomputable def InvAtom :=
  {A : Finset Q60 // ∃ x : Q60, x ≠ 1 ∧ A = ({x, x⁻¹} : Finset Q60)}

noncomputable def ConnectionSet :=
  {S : Finset Q60 // 1 ∉ S ∧ ∀ x : Q60, x ∈ S → x⁻¹ ∈ S}

noncomputable instance : Finite InvAtom :=
  Finite.of_injective (fun A : InvAtom => A.1) (fun _ _ h => Subtype.ext h)
noncomputable instance : Finite ConnectionSet :=
  Finite.of_injective (fun S : ConnectionSet => S.1) (fun _ _ h => Subtype.ext h)
noncomputable instance : Fintype InvAtom := Fintype.ofFinite InvAtom
noncomputable instance : Fintype ConnectionSet := Fintype.ofFinite ConnectionSet

noncomputable def connectionAtoms (S : ConnectionSet) : Finset InvAtom := by
  classical
  exact Finset.univ.filter (fun A => A.1 ⊆ S.1)

def claim25590 : Prop :=
  Fintype.card InvAtom = 30 ∧
  ∃ e : ConnectionSet ≃ Finset InvAtom,
    ∀ S : ConnectionSet, e S = connectionAtoms S

def claim25591 : Prop :=
  Fintype.card ConnectionSet = 2 ^ 30 ∧
  Fintype.card ConnectionSet = 1073741824

abbrev Q60Aut := Q60 ≃* Q60

noncomputable def mapAtom (α : Q60Aut) (A : InvAtom) : InvAtom := by
  classical
  refine ⟨A.1.image α, ?_⟩
  rcases A.2 with ⟨x, hx, hA⟩
  refine ⟨α x, ?_, ?_⟩
  · intro h
    apply hx
    apply α.injective
    simpa using h
  · rw [hA]
    simp

def claim25592 : Prop :=
  Fintype.card Q60Aut = 240 ∧
  ∃ (ρ : Q60Aut →* Equiv.Perm InvAtom),
    (∀ (α : Q60Aut) (A : InvAtom), ρ α A = mapAtom α A) ∧
    Nat.card (MonoidHom.ker ρ) = 2 ∧
    Nat.card (MonoidHom.range ρ) = 120 ∧
    ∃ τ : Q60Aut,
      τ ≠ 1 ∧ τ qa = qa ∧ τ qb = qa ^ 15 * qb ∧
        MonoidHom.ker ρ = Subgroup.closure ({τ} : Set Q60Aut)

noncomputable def powerAction (ρ : Q60Aut →* Equiv.Perm InvAtom)
    (α : Q60Aut) (S : Finset InvAtom) : Finset InvAtom := by
  classical
  exact S.image (ρ α)

noncomputable def powerOrbitSetoid (ρ : Q60Aut →* Equiv.Perm InvAtom) :
    Setoid (Finset InvAtom) where
  r S T := ∃ α : Q60Aut, powerAction ρ α S = T
  iseqv := by
    classical
    constructor
    · intro S
      refine ⟨1, ?_⟩
      simp [powerAction]
    · intro S T h
      rcases h with ⟨α, hα⟩
      refine ⟨α⁻¹, ?_⟩
      rw [← hα]
      have hperm : ρ α⁻¹ * ρ α = 1 := by
        rw [← ρ.map_mul, inv_mul_cancel, ρ.map_one]
      have himage := congrArg (fun p : Equiv.Perm InvAtom => S.image p) hperm
      simpa [powerAction, Finset.image_image] using himage
    · intro S T U hST hTU
      rcases hST with ⟨α, rfl⟩
      rcases hTU with ⟨β, hβ⟩
      refine ⟨β * α, ?_⟩
      rw [← hβ]
      simp only [powerAction, Finset.image_image, map_mul]
      rfl

def claim25594 : Prop :=
  ∃ (ρ : Q60Aut →* Equiv.Perm InvAtom),
    (∀ (α : Q60Aut) (A : InvAtom), ρ α A = mapAtom α A) ∧
    Nat.card (MonoidHom.range ρ) = 120 ∧
    Nat.card (Quotient (powerOrbitSetoid ρ)) = 10127104

def cayleyGraph (S : ConnectionSet) : SimpleGraph Q60 where
  Adj x y := x⁻¹ * y ∈ S.1
  symm := ⟨by
    intro x y h
    simpa [inv_mul_cancel_left] using S.2.2 (x⁻¹ * y) h⟩
  loopless := ⟨by
    intro x h
    exact S.2.1 (by simpa using h)⟩

def claim25597 : Prop :=
  ∀ (S T : ConnectionSet),
    Nonempty (SimpleGraph.Iso (cayleyGraph S) (cayleyGraph T)) →
      ∃ α : Q60Aut, S.1.image α = T.1

def graphIsoRel (S T : ConnectionSet) : Prop :=
  Nonempty (SimpleGraph.Iso (cayleyGraph S) (cayleyGraph T))

noncomputable def graphIsoSetoid : Setoid ConnectionSet where
  r := graphIsoRel
  iseqv := by
    constructor
    · intro S
      exact ⟨SimpleGraph.Iso.refl⟩
    · intro S T h
      rcases h with ⟨f⟩
      exact ⟨f.symm⟩
    · intro S T U hST hTU
      rcases hST with ⟨f⟩
      rcases hTU with ⟨g⟩
      exact ⟨RelIso.trans f g⟩

def claim25596 : Prop :=
  Nat.card (Quotient graphIsoSetoid) = 10127104 ∧
  ∀ (S T : ConnectionSet), graphIsoRel S T →
    ∃ α : Q60Aut, S.1.image α = T.1

end MathlibPlus.Open.Q60Batch
