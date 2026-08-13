import Mathlib

namespace MathlibPlus.LinearAlgebra.Claim53182

private def goodDir {K U : Type*} [AddGroup U] [AddGroup K]
    (f : U → K) (a : U) : Prop :=
  ∀ x, f (x + a) - f x - f a = 0

private lemma goodDir_zero {K U : Type*} [AddGroup U] [AddGroup K]
    (f : U → K) (h0 : f 0 = 0) : goodDir f 0 := by
  intro x
  simp [h0]

private lemma goodDir_add {K U : Type*} [AddCommGroup U] [AddCommGroup K]
    (f : U → K) {a b : U} (ha : goodDir f a) (hb : goodDir f b) :
    goodDir f (a + b) := by
  intro x
  have hxa := ha x
  have hxb := hb (x + a)
  have hab := ha b
  rw [sub_eq_zero] at hxa hxb hab ⊢
  have hxb' : f (x + (a + b)) - f (x + a) = f b := by
    simpa only [add_assoc] using hxb
  have hab' : f (a + b) = f a + f b := by
    calc
      f (a + b) = f (b + a) := by rw [add_comm]
      _ = (f (b + a) - f b) + f b := by abel
      _ = f a + f b := by rw [hab]
  calc
    f (x + (a + b)) - f x =
        (f (x + (a + b)) - f (x + a)) +
          (f (x + a) - f x) := by abel
    _ = f b + f a := by rw [hxb', hxa]
    _ = f a + f b := by abel
    _ = f (a + b) := hab'.symm

private lemma goodDir_neg {K U : Type*} [AddCommGroup U] [AddCommGroup K]
    (f : U → K) {a : U} (ha : goodDir f a)
    (hneg : f (-a) = -f a) : goodDir f (-a) := by
  intro x
  have h := ha (x - a)
  rw [sub_eq_zero] at h ⊢
  have hxa : f x - f (x - a) = f a := by
    simpa [sub_eq_add_neg] using h
  calc
    f (x + -a) - f x = -(f x - f (x + -a)) := by abel
    _ = -f a := by rw [show f x - f (x + -a) = f a by simpa [sub_eq_add_neg] using hxa]
    _ = f (-a) := hneg.symm

private def goodDirAddSubgroup {K U : Type*} [AddCommGroup U] [AddCommGroup K]
    (f : U → K) (h0 : f 0 = 0) (hneg : ∀ a, f (-a) = -f a) : AddSubgroup U :=
  { carrier := {a | goodDir f a}
    zero_mem' := goodDir_zero f h0
    add_mem' := by
      intro a b ha hb
      exact goodDir_add f ha hb
    neg_mem' := by
      intro a ha
      exact goodDir_neg f ha (hneg a) }

private def goodDirSubmodule {p : ℕ} {U : Type*} [AddCommGroup U]
    [Module (ZMod p) U] {f : U → ZMod p} (h0 : f 0 = 0)
    (hneg : ∀ a, f (-a) = -f a) : Submodule (ZMod p) U := by
  let A := goodDirAddSubgroup f h0 hneg
  exact
    { carrier := A
      zero_mem' := A.zero_mem
      add_mem' := A.add_mem
      smul_mem' := by
        intro c a ha
        exact zmod_smul_mem (K := A) ha c }

private lemma goodDir_add_iff {K U : Type*} [AddCommGroup U] [AddCommGroup K]
    (f : U → K) {a b : U} (ha : goodDir f a) :
    f (a + b) = f a + f b := by
  have h := ha b
  rw [sub_eq_zero] at h
  calc
    f (a + b) = f (b + a) := by rw [add_comm]
    _ = (f (b + a) - f b) + f b := by abel
    _ = f a + f b := by rw [h]

private def goodDirAddMap {p : ℕ} {U : Type*} [AddCommGroup U]
    [Module (ZMod p) U] {f : U → ZMod p}
    (Z : Submodule (ZMod p) U) (h0 : f 0 = 0)
    (hgood : ∀ a : Z, goodDir f a.1) : Z →+ ZMod p :=
  { toFun := fun a => f a.1
    map_zero' := h0
    map_add' := by
      intro a b
      exact goodDir_add_iff f (hgood a) }

private def goodDirLinearMap {p : ℕ} {U : Type*} [AddCommGroup U]
    [Module (ZMod p) U] {f : U → ZMod p}
    (Z : Submodule (ZMod p) U) (h0 : f 0 = 0)
    (hgood : ∀ a : Z, goodDir f a.1) :
    Z →ₗ[ZMod p] ZMod p :=
  { toFun := goodDirAddMap Z h0 hgood
    map_add' := (goodDirAddMap Z h0 hgood).map_add
    map_smul' := by
      intro c a
      obtain ⟨n, rfl⟩ := ZMod.intCast_surjective c
      change (goodDirAddMap Z h0 hgood) ((n : ZMod p) • a) =
        (n : ZMod p) • (goodDirAddMap Z h0 hgood) a
      rw [Int.cast_smul_eq_zsmul, (goodDirAddMap Z h0 hgood).map_zsmul,
        Int.cast_smul_eq_zsmul] }

/-- The quiet-direction set is a `ZMod p`-subspace, restriction of `f` is
linear there, and that linear map extends to the ambient finite-dimensional
space. -/
theorem quietDirection_linearShadow_claim53182
    (p : ℕ) [Fact p.Prime] (_hpodd : Odd p)
    {U : Type*} [AddCommGroup U] [Module (ZMod p) U]
    [FiniteDimensional (ZMod p) U]
    (f : U → ZMod p) (h0 : f 0 = 0)
    (hneg : ∀ a, f (-a) = -f a) :
    ∃ Z : Submodule (ZMod p) U,
      (∀ a, a ∈ Z ↔ ∀ x, f (x + a) - f x - f a = 0) ∧
      ∃ ℓ : U →ₗ[ZMod p] ZMod p, ∀ a : Z, ℓ a = f a.1 := by
  let Z := goodDirSubmodule h0 hneg
  have hchar : ∀ a : Z, goodDir f a.1 := by
    intro a
    exact a.2
  let g := goodDirLinearMap Z h0 hchar
  obtain ⟨ℓ, hℓ⟩ := LinearMap.exists_extend g
  refine ⟨Z, ?_, ℓ, ?_⟩
  · intro a
    change a ∈ goodDirSubmodule h0 hneg ↔ _
    rfl
  · intro a
    have ha := congrArg (fun h : Z →ₗ[ZMod p] ZMod p => h a) hℓ
    simpa [g, goodDirLinearMap, goodDirAddMap] using ha

end MathlibPlus.LinearAlgebra.Claim53182
