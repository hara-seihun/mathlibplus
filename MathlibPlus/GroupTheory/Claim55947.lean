import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic

namespace MathlibPlus.GroupTheory.Claim55947

/--
The affine order-three fixed-point calculation from claim 55947.
The additive group is the correction module; the displayed equation is the
fixed-point convention `A e + d = e`.
-/
theorem affine_order_three_fixed_point
    {L : Type*} [AddCommGroup L] [Finite L]
    (hcard : Nat.Coprime 3 (Nat.card L))
    (A : L ≃+ L) (d e : L)
    (_hA : ∀ x : L, A (A (A x)) = x)
    (hd : d + A d + A (A d) = 0)
    (he : 3 • e = 2 • d + A d) :
    e - A e = d ∧ A e + d = e := by
  have hA2 : A (A d) = -d - A d := by
    calc
      A (A d) = -(d + A d) := eq_neg_of_add_eq_zero_right hd
      _ = -d - A d := by abel
  have hthree : Function.Injective (fun x : L => 3 • x) :=
    (hcard.symm.nsmul_right_bijective (G := L) (n := 3)).injective
  have hmul : 3 • (e - A e) = 3 • d := by
    rw [nsmul_sub, he, ← map_nsmul, he]
    rw [map_add, map_nsmul, hA2]
    abel
  have hdiff : e - A e = d := hthree hmul
  have hfix : A e + d = e := by
    calc
      A e + d = A e + (e - A e) := by rw [hdiff]
      _ = e := by abel
  exact ⟨hdiff, hfix⟩

/-- The equation defining the fixed point has a unique solution on a 3-prime module. -/
theorem affine_order_three_fixed_point_unique
    {L : Type*} [AddCommGroup L] [Finite L]
    (hcard : Nat.Coprime 3 (Nat.card L))
    (A : L ≃+ L) (d : L) :
    ∃! e : L, 3 • e = 2 • d + A d := by
  obtain ⟨e, he⟩ :=
    (hcard.symm.nsmul_right_bijective (G := L) (n := 3)).surjective (2 • d + A d)
  have he3 : 3 • e = 2 • d + A d := by simpa using he
  refine ⟨e, he3, ?_⟩
  intro e' he'
  apply (hcard.symm.nsmul_right_bijective (G := L) (n := 3)).injective
  change 3 • e' = 3 • e
  rw [he3, he']

end MathlibPlus.GroupTheory.Claim55947
