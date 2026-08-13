import Mathlib

namespace MathlibPlus.GroupTheory

section

local notation "Q8" => QuaternionGroup 2
local notation "S3" => Equiv.Perm (Fin 3)

private theorem q8_fourth (x : Q8) : x ^ 4 = 1 := by
  have he : Monoid.exponent Q8 = 4 := by
    norm_num [QuaternionGroup.exponent, Nat.lcm]
  rw [← he]
  exact Monoid.pow_exponent_eq_one x

private theorem q8_square_classification :
    ∀ x : Q8, x ^ 2 = 1 → x = 1 ∨ x = QuaternionGroup.a 2 := by
  native_decide

private theorem q8_order_four_of_square_ne_one (x : Q8) (hx : x ^ 2 ≠ 1) :
    orderOf x = 4 := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply orderOf_eq_prime_pow (n := 1) (p := 2)
  · simpa [pow_two] using hx
  · simpa [pow_succ, pow_two] using q8_fourth x

private theorem q8_unique_involution :
    ∀ x : Q8, x ^ 2 ≠ 1 → ∀ y : Q8, y ≠ 1 → y ^ 2 = 1 →
      y = x ^ 2 := by
  native_decide

/-- The Q₈-to-S₃ projection core of admitted claim 29192.  Every homomorphism
from Q₈ to S₃ has image of order at most two; its kernel therefore contains a
nontrivial order-four element, whose square is the unique nontrivial element
of order at most two in Q₈. -/
theorem q8_to_s3_projection_has_large_kernel_claim29192
    (f : QuaternionGroup 2 →* Equiv.Perm (Fin 3)) :
    Nat.card f.range ≤ 2 ∧
      4 ≤ Nat.card f.ker ∧
      ∃ x : QuaternionGroup 2,
        x ∈ f.ker ∧
        orderOf x = 4 ∧
        x ^ 2 ≠ 1 ∧
        (∀ y : QuaternionGroup 2, y ≠ 1 → y ^ 2 = 1 → y = x ^ 2) := by
  have h8 : Nat.card f.range ∣ Nat.card (QuaternionGroup 2) :=
    Subgroup.card_range_dvd f
  have h6 : Nat.card f.range ∣ Nat.card (Equiv.Perm (Fin 3)) :=
    Subgroup.card_subgroup_dvd_card f.range
  have h8' : Nat.card f.range ∣ 8 := by
    simpa [Nat.card_eq_fintype_card, QuaternionGroup.card] using h8
  have h6' : Nat.card f.range ∣ 6 := by
    convert h6 using 1 <;>
      norm_num [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
  have hr : Nat.card f.range ≤ 8 := Nat.le_of_dvd (by omega) h8'
  have hrange : Nat.card f.range ≤ 2 := by
    interval_cases h : Nat.card f.range
    all_goals try { norm_num at h8' h6' }
    all_goals omega
  have hprod : Nat.card f.ker * Nat.card f.range = 8 := by
    have h := Subgroup.card_mul_index f.ker
    rw [Subgroup.index_ker] at h
    simpa [Nat.card_eq_fintype_card, QuaternionGroup.card] using h
  have hrpos : 0 < Nat.card f.range := Nat.card_pos
  have hker : 4 ≤ Nat.card f.ker := by
    have hc : Nat.card f.range = 1 ∨ Nat.card f.range = 2 := by omega
    rcases hc with hc | hc
    · have h := hprod
      rw [hc] at h
      norm_num at h
      have hp : Nat.card f.ker = 8 := by simpa using h
      omega
    · have h := hprod
      rw [hc] at h
      norm_num at h
      have hp : Nat.card f.ker * 2 = 8 := by simpa using h
      omega
  have hx : ∃ x : Q8, x ∈ f.ker ∧ x ^ 2 ≠ 1 := by
    by_contra hn
    push_neg at hn
    have hsub : (f.ker : Set Q8) ⊆
        (↑({1, QuaternionGroup.a 2} : Finset Q8) : Set Q8) := by
      intro x hx
      have hs : x ^ 2 = 1 := hn x hx
      simpa [Finset.mem_insert, Finset.mem_singleton] using
        (q8_square_classification x hs)
    let emb : f.ker → ({1, QuaternionGroup.a 2} : Finset Q8) := fun x =>
      ⟨x.1, hsub x.2⟩
    have hemb : Function.Injective emb := by
      intro a b hab
      apply Subtype.ext
      exact congrArg
        (fun z : ({1, QuaternionGroup.a 2} : Finset Q8) => (z : Q8)) hab
    have hcard : Nat.card f.ker ≤
        Nat.card ({1, QuaternionGroup.a 2} : Finset Q8) :=
      Nat.card_le_card_of_injective emb hemb
    have htwo : Nat.card ({1, QuaternionGroup.a 2} : Finset Q8) = 2 := by
      simp [Nat.card_eq_fintype_card]
      native_decide
    omega
  rcases hx with ⟨x, hxker, hxnot⟩
  refine ⟨hrange, hker, x, hxker,
    q8_order_four_of_square_ne_one x hxnot, hxnot, ?_⟩
  exact q8_unique_involution x hxnot

end

end MathlibPlus.GroupTheory
