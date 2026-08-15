import Mathlib

noncomputable section
open scoped BigOperators
open Set MeasureTheory

namespace MathlibPlus.Open.ResearchFormalization.Batch

/-- The vector space and inverse-pair atoms for the five-color claims. -/
abbrev V5 := Fin 2 → ZMod 5

def isLinear5 (A : V5 → V5) : Prop :=
  (∀ x y, A (x + y) = A x + A y) ∧
  (∀ (c : ZMod 5) x, A (c • x) = c • A x)

def isGL5 (A : V5 → V5) : Prop := isLinear5 A ∧ Function.Bijective A
abbrev GL5 := {A : V5 → V5 // isGL5 A}
instance : Finite GL5 :=
  Finite.of_injective (fun A : GL5 => A.1) Subtype.val_injective
noncomputable instance : Fintype GL5 := Fintype.ofFinite GL5

def isAtom5 (a : Finset V5) : Prop :=
  a.card = 2 ∧ ∃ x : V5, x ≠ 0 ∧ a = {x, -x}

abbrev Atom5 := {a : Finset V5 // isAtom5 a}
instance : Finite Atom5 :=
  Finite.of_injective (fun a : Atom5 => a.1) Subtype.val_injective
noncomputable instance : Fintype Atom5 := Fintype.ofFinite Atom5
abbrev Profile5 := Atom5 → Fin 5

def linearImageAtom5 (A : GL5) (a : Atom5) : Atom5 := by
  let x : V5 := Classical.choose a.property.2
  have hx : x ≠ 0 := (Classical.choose_spec a.property.2).1
  have hax : a.1 = {x, -x} := (Classical.choose_spec a.property.2).2
  refine ⟨a.1.image A.1, ?_⟩
  constructor
  · rw [Finset.card_image_of_injective _ A.property.2.1, a.property.1]
  · refine ⟨A.1 x, ?_, ?_⟩
    · intro h
      apply hx
      have hzero : A.1 0 = 0 := by
        have hzero' := A.property.1.1 0 0
        have hzero'' : 0 + A.1 0 = A.1 0 + A.1 0 := by
          simpa using hzero'
        exact (add_right_cancel hzero'').symm
      apply A.property.2.1
      simpa [hzero] using h
    · rw [hax, Finset.image_insert, Finset.image_singleton]
      have hneg : A.1 (-x) = -A.1 x := by
        simpa using A.property.1.2 (-1 : ZMod 5) x
      simp [hneg]

def profilePrecompose5 (A : GL5) (f : Profile5) : Profile5 :=
  f ∘ linearImageAtom5 A

def constantProfile5 (c : Fin 5) : Profile5 := fun _ => c

def atomActionImage5 : Finset (Atom5 → Atom5) :=
  Finset.univ.image linearImageAtom5

def atomActionKernel5 : Set GL5 :=
  {A | ∀ a, linearImageAtom5 A a = a}

def identityGL5 : GL5 :=
  ⟨fun x => x,
    ⟨⟨by intros; rfl, by intros; rfl⟩, Function.bijective_id⟩⟩

def negIdentityGL5 : GL5 :=
  ⟨fun x => -x,
    ⟨⟨by
        intro x y
        simp [add_comm],
      by
        intro c x
        simp [smul_neg]⟩,
      (show Function.Involutive (fun x : V5 => -x) from by
        intro x
        simp).bijective⟩⟩

noncomputable instance : Fintype {A : GL5 // A ∈ atomActionKernel5} :=
  Fintype.ofFinite _

def claim32695 : Prop :=
  Fintype.card Atom5 = 12 ∧
    Fintype.card Profile5 = (5 : ℕ) ^ 12 ∧
    (∀ c : Fin 5, ∃ f : Profile5, ∀ a, f a = c) ∧
    (∃ f : Profile5, ¬Function.Surjective f) ∧
    (∀ c d : Fin 5, c ≠ d → constantProfile5 c ≠ constantProfile5 d)

def claim32697 : Prop :=
  Fintype.card GL5 = 480 ∧
    Fintype.card {A : GL5 // A ∈ atomActionKernel5} = 2 ∧
    (∀ A : GL5, A ∈ atomActionKernel5 ↔
      A = identityGL5 ∨ A = negIdentityGL5) ∧
    atomActionImage5.card = 240 ∧
    (∀ A : GL5, ∀ f : Profile5, ∀ a : Atom5,
      profilePrecompose5 A f a = f (linearImageAtom5 A a))

def orbitRepresentativeSystem5 (N : ℕ) : Prop :=
  ∃ reps : Fin N → Profile5,
    ∀ f : Profile5, ∃! i : Fin N, ∃ A : GL5,
      f = profilePrecompose5 A (reps i)

def claim32698 : Prop :=
  Fintype.card Profile5 = 244140625 ∧ orbitRepresentativeSystem5 1043620

def colorComplement5 (c : Fin 5) : Fin 5 :=
  ⟨4 - c.1, by omega⟩

def profileComplement5 (f : Profile5) : Profile5 :=
  fun a => colorComplement5 (f a)

def claim32702 : Prop :=
  Function.Involutive colorComplement5 ∧
    Function.Involutive profileComplement5 ∧
    (∀ A : GL5, ∀ f : Profile5,
      profileComplement5 (profilePrecompose5 A f) =
        profilePrecompose5 A (profileComplement5 f)) ∧
    ∃ reps : Fin 1043620 → Profile5,
      (∀ f : Profile5, ∃! i : Fin 1043620, ∃ A : GL5,
        f = profilePrecompose5 A (reps i)) ∧
      (∀ i : Fin 1043620, ∀ A : GL5, ∀ a : Atom5,
        profileComplement5 (profilePrecompose5 A (reps i)) a =
          profilePrecompose5 A (profileComplement5 (reps i)) a)
end MathlibPlus.Open.ResearchFormalization.Batch
