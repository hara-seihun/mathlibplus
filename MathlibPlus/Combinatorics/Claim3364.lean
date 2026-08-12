import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.SDiff

namespace MathlibPlus.Combinatorics.Claim3364

/-!
Formalization of admitted claim 3364 (packet `C-0230`).  A finite ground set
and finite family are represented by `Finset`s.  The principal-filter
convention used for the frequency identity is reverse inclusion: the filter
at `X.erase x` is represented by the members `B ⊆ X.erase x`.
-/

/-- Relative complement in a finite ground set. -/
def relativeComplement {α : Type*} [DecidableEq α]
    (X A : Finset α) : Finset α := X \ A

/-- The complement family `L = {X \ A : A ∈ F}`. -/
def complementFamily {α : Type*} [DecidableEq α]
    (X : Finset α) (F : Finset (Finset α)) : Finset (Finset α) :=
  F.image (relativeComplement X)

/-- Frequency of a ground element in a finite family. -/
def memberFrequency {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (x : α) : ℕ :=
  (F.filter (fun A => x ∈ A)).card

/-- The corresponding principal-filter size in the reverse-inclusion lattice. -/
def principalFilterSize {α : Type*} [DecidableEq α]
    (X : Finset α) (F : Finset (Finset α)) (x : α) : ℕ :=
  ((complementFamily X F).filter (fun B => B ⊆ X.erase x)).card

/-- Complements of a union-closed family are closed under intersection. -/
theorem complementFamily_intersection_closed
    {α : Type*} [DecidableEq α] (X : Finset α) (F : Finset (Finset α))
    (_hsub : ∀ A ∈ F, A ⊆ X)
    (hunion : ∀ A ∈ F, ∀ B ∈ F, A ∪ B ∈ F) :
    ∀ B ∈ complementFamily X F, ∀ C ∈ complementFamily X F,
      B ∩ C ∈ complementFamily X F := by
  classical
  intro B hB C hC
  rcases Finset.mem_image.mp hB with ⟨A, hAF, rfl⟩
  rcases Finset.mem_image.mp hC with ⟨D, hDF, rfl⟩
  change (X \ A) ∩ (X \ D) ∈ F.image (relativeComplement X)
  rw [← Finset.sdiff_union_distrib]
  exact Finset.mem_image.mpr ⟨A ∪ D, hunion A hAF D hDF, rfl⟩

/-- The complement map preserves family cardinality on subsets of `X`. -/
theorem complementFamily_card_preserves
    {α : Type*} [DecidableEq α] (X : Finset α) (F : Finset (Finset α))
    (hsub : ∀ A ∈ F, A ⊆ X) :
    (complementFamily X F).card = F.card := by
  classical
  apply Finset.card_image_of_injOn
  intro A hAF B hBF heq
  have heq' := congrArg (fun T : Finset α => X \ T) heq
  simpa [relativeComplement, Finset.sdiff_sdiff_eq_self (hsub A hAF),
    Finset.sdiff_sdiff_eq_self (hsub B hBF)] using heq'

/-- The elementary predicate behind the frequency/filter correspondence. -/
theorem complement_predicate
    {α : Type*} [DecidableEq α] (X A : Finset α) (x : α)
    (_hA : A ⊆ X) (hxX : x ∈ X) :
    X \ A ⊆ X.erase x ↔ x ∈ A := by
  constructor
  · intro h
    by_contra hx
    have hxcomp : x ∈ X \ A := by simp [hxX, hx]
    have hxerase : x ∉ X.erase x := by simp
    exact hxerase (h hxcomp)
  · intro hx y hy
    have hyX : y ∈ X := (Finset.mem_sdiff.mp hy).1
    have hyA : y ∉ A := (Finset.mem_sdiff.mp hy).2
    simp only [Finset.mem_erase]
    constructor
    · intro hxy
      apply hyA
      simpa [hxy] using hx
    · exact hyX

/-- Frequencies in `F` equal reverse-inclusion principal-filter sizes in `L`. -/
theorem principalFilterSize_eq_frequency
    {α : Type*} [DecidableEq α] (X : Finset α) (F : Finset (Finset α))
    (hsub : ∀ A ∈ F, A ⊆ X) (x : α) (hxX : x ∈ X) :
    principalFilterSize X F x = memberFrequency F x := by
  classical
  have hfilter :
      (complementFamily X F).filter (fun B => B ⊆ X.erase x) =
        (F.filter (fun A => x ∈ A)).image (relativeComplement X) := by
    rw [complementFamily, Finset.filter_image]
    congr 1
    apply Finset.filter_congr
    intro A hAF
    exact complement_predicate X A x (hsub A hAF) hxX
  rw [principalFilterSize, hfilter]
  apply Finset.card_image_of_injOn
  intro A hAF B hBF heq
  have hA := hsub A (Finset.mem_of_mem_filter A hAF)
  have hB := hsub B (Finset.mem_of_mem_filter B hBF)
  have heq' : X \ (X \ A) = X \ (X \ B) := by
    simpa [relativeComplement] using congrArg (fun T : Finset α => X \ T) heq
  calc
    A = X \ (X \ A) := (Finset.sdiff_sdiff_eq_self hA).symm
    _ = X \ (X \ B) := heq'
    _ = B := Finset.sdiff_sdiff_eq_self hB

end MathlibPlus.Combinatorics.Claim3364
