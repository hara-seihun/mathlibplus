import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image

namespace MathlibPlus
namespace Combinatorics

/--
For an idempotent self-map of a finite type, the image is exactly the set of
fixed points, so the cardinality excess is the number of non-fixed sources.
-/
theorem image_eq_fixed_of_idempotent
    {α : Type*} [Fintype α] [DecidableEq α]
    (f : α → α) (hidem : ∀ x, f (f x) = f x) :
    Finset.univ.image f = Finset.univ.filter (fun x => f x = x) := by
  ext x
  constructor
  · intro hx
    rcases Finset.mem_image.mp hx with ⟨y, hy, hfy⟩
    have hfix : f x = x := by
      rw [← hfy]
      exact hidem y
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hfix⟩
  · intro hx
    rcases Finset.mem_filter.mp hx with ⟨_, hfix⟩
    exact Finset.mem_image.mpr ⟨x, Finset.mem_univ _, hfix⟩

theorem card_sub_card_image_eq_card_nonfixed
    {α : Type*} [Fintype α] [DecidableEq α]
    (f : α → α) (hidem : ∀ x, f (f x) = f x) :
    Fintype.card α - (Finset.univ.image f).card =
      (Finset.univ.filter (fun x => f x ≠ x)).card := by
  let fixed : Finset α := Finset.univ.filter (fun x => f x = x)
  have himage : Finset.univ.image f = fixed := by
    simpa [fixed] using image_eq_fixed_of_idempotent f hidem
  have hpartition :=
    Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset α))
      (fun x : α => f x = x)
  have hcard :
      (Finset.univ.filter (fun x => f x ≠ x)).card + fixed.card =
        (Finset.univ : Finset α).card := by
    simpa [fixed, Nat.add_comm] using hpartition
  rw [himage]
  exact (Nat.eq_sub_of_add_eq hcard).symm

/--
For a finite family of finite sets, the non-fixed members of the union map
`A ↦ A ∪ R` are precisely the members that do not contain `R`.
-/
theorem card_nonfixed_union_eq_card_not_subset
    {α : Type*} [DecidableEq α]
    (S : Finset (Finset α)) (R : Finset α)
    (_hclosed : ∀ A ∈ S, A ∪ R ∈ S) :
    (S.filter (fun A => A ∪ R ≠ A)).card =
      (S.filter (fun A => ¬ R ⊆ A)).card := by
  have hfilter :
      S.filter (fun A => A ∪ R ≠ A) =
        S.filter (fun A => ¬ R ⊆ A) := by
    apply Finset.filter_congr
    intro A hA
    simp [Finset.union_eq_left]
  exact congrArg Finset.card hfilter

end Combinatorics
end MathlibPlus
