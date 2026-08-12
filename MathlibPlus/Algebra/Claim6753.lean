import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Card

open scoped BigOperators

namespace MathlibPlus.Algebra.Claim6753

noncomputable section

/-- Number of ordered pairs from `S` whose sum is `g`. -/
def pairCount {G : Type*} [AddCommMonoid G] [DecidableEq G]
    (S : Finset G) (g : G) : ℕ :=
  ((S.product S).filter (fun p : G × G => p.1 + p.2 = g)).card

/-- The indicator sum is the cardinality of the ordered-pair fibre. -/
theorem pairCount_eq_card_filter {G : Type*} [AddCommMonoid G] [DecidableEq G]
    (S : Finset G) (g : G) :
    pairCount S g = ((S.product S).filter (fun p : G × G => p.1 + p.2 = g)).card := by
  simp [pairCount]

/-- The multiset of pair-count values, with one entry for every group element. -/
def convolutionProfile {G : Type*} [AddCommMonoid G] [Fintype G] [DecidableEq G]
    (S : Finset G) : Multiset ℕ :=
  (Finset.univ : Finset G).val.map (pairCount S)

/-- The group-algebra element supported on a finite subset. -/
def indicatorElement {G : Type*} [AddCommMonoid G]
    (S : Finset G) : AddMonoidAlgebra ℕ G := by
  classical
  exact AddMonoidAlgebra.ofCoeff
    { support := S
      toFun := fun a => if a ∈ S then 1 else 0
      mem_support_toFun := by
        intro a
        simp }

/-- The indicator element is the finite basis sum from the source notation. -/
theorem indicatorElement_eq_sum {G : Type*} [AddCommMonoid G]
    (S : Finset G) :
    indicatorElement S = ∑ s ∈ S, AddMonoidAlgebra.single s 1 := by
  classical
  ext g
  simp [indicatorElement, Finsupp.single_apply]

 theorem indicatorElement_sq_eq_convolution
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G] (S : Finset G) :
    indicatorElement S * indicatorElement S =
      ∑ g : G, AddMonoidAlgebra.single g (pairCount S g) := by
  classical
  ext g
  have hcoeff :
      (indicatorElement S * indicatorElement S).coeff g =
        ∑ a ∈ S, ∑ x ∈ S,
          if a + x = g ∧ x ∈ S ∧ a ∈ S then 1 else 0 := by
    simp only [indicatorElement, AddMonoidAlgebra.coeff_mul,
      Finsupp.sum]
    apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro x hx
    simp [ha, hx]
  have hdrop :
      (∑ a ∈ S, ∑ x ∈ S,
          if a + x = g ∧ x ∈ S ∧ a ∈ S then 1 else 0) =
        ∑ a ∈ S, ∑ x ∈ S, if a + x = g then 1 else 0 := by
    apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro x hx
    simp [ha, hx]
  have hcard :
      (∑ a ∈ S, ∑ x ∈ S, if a + x = g then 1 else 0) =
        ((S.product S).filter (fun p : G × G => p.1 + p.2 = g)).card := by
    rw [← Finset.sum_product S S
      (fun p : G × G => if p.1 + p.2 = g then 1 else 0)]
    exact Finset.sum_boole (R := ℕ)
      (fun p : G × G => p.1 + p.2 = g) (S.product S)
  have hright :
      (∑ c : G, AddMonoidAlgebra.single c (pairCount S c)).coeff g =
        pairCount S g := by
    simp [Finsupp.single_apply, Finset.sum_ite_eq']
  rw [hcoeff, hdrop, hcard, hright]; rfl

end
end MathlibPlus.Algebra.Claim6753
