import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Lemmas
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

open scoped BigOperators

namespace MathlibPlus.NumberTheory

/--
Claim 44305 (packet `R-2895`): after clearing the common factor `2⁻ⁿ`, a
finite positive-offset representation of `n / 2ⁿ` is exactly the displayed
offset equation.  The hypotheses retain the packet's `n ≥ 3` and positive
finite-offset domain, even though the algebraic equivalence itself is more
general.
-/
theorem claim44305_dyadic_offset_normal_form
    (n : ℕ) (D : Finset ℕ) (hn : 3 ≤ n)
    (hD : ∀ d ∈ D, 0 < d) :
    ((n : ℚ) / (2 : ℚ)^n =
        ∑ d ∈ D, (n + d : ℚ) / (2 : ℚ)^(n + d)) ↔
      (n : ℚ) = ∑ d ∈ D, (n + d : ℚ) / (2 : ℚ)^d := by
  have hpow (k : ℕ) : (2 : ℚ)^k ≠ 0 := pow_ne_zero _ (by norm_num)
  have hleft : ((n : ℚ) / (2 : ℚ)^n) * (2 : ℚ)^n = n := by
    field_simp
  have hright (d : ℕ) :
      ((n + d : ℚ) / (2 : ℚ)^(n + d)) * (2 : ℚ)^n =
        (n + d : ℚ) / (2 : ℚ)^d := by
    rw [pow_add]
    field_simp
  have hright' (d : ℕ) :
      ((n + d : ℚ) / (2 : ℚ)^d) / (2 : ℚ)^n =
        (n + d : ℚ) / (2 : ℚ)^(n + d) := by
    rw [pow_add]
    field_simp
  constructor
  · intro h
    have h' := congrArg (fun x : ℚ => x * (2 : ℚ)^n) h
    simpa [Finset.sum_mul, hleft, hright] using h'
  · intro h
    have h' := congrArg (fun x : ℚ => x / (2 : ℚ)^n) h
    simpa [Finset.sum_div, hright'] using h'

/--
Claim 44305 (packet `R-2895`): a representation by distinct positive
indices other than `n` can use only indices strictly later than `n`.
-/
theorem claim44305_representation_uses_later
    (n : ℕ) (S : Finset ℕ) (hn : 3 ≤ n)
    (hpos : ∀ a ∈ S, 0 < a) (hnot : n ∉ S)
    (hrep : (n : ℚ) / (2 : ℚ)^n =
      ∑ a ∈ S, (a : ℚ) / (2 : ℚ)^a) :
    ∀ a ∈ S, n < a := by
  have step (k : ℕ) (hk : 2 ≤ k) :
      (k + 1 : ℚ) / (2 : ℚ)^(k + 1) < (k : ℚ) / (2 : ℚ)^k := by
    rw [pow_succ]
    have hp : 0 < (2 : ℚ)^k := by positivity
    apply (div_lt_iff₀ (mul_pos hp (by norm_num : (0 : ℚ) < 2))).2
    have hkq : (1 : ℚ) < k := by exact_mod_cast (show 1 < k by omega)
    field_simp
    linarith
  have mono (m : ℕ) (hm : 3 ≤ m) (a : ℕ) (ha : 2 ≤ a) (hal : a < m) :
      (m : ℚ) / (2 : ℚ)^m < (a : ℚ) / (2 : ℚ)^a := by
    revert hm a ha hal
    induction m with
    | zero => intro; omega
    | succ m ih =>
        intro hm a ha hal
        by_cases h : a = m
        · subst m
          simpa [Nat.cast_add] using step a (by omega)
        · have hlt : a < m := by omega
          exact lt_trans (by simpa [Nat.cast_add] using step m (by omega))
            (ih (by omega) a ha hlt)
  have lower (m : ℕ) (hm : 3 ≤ m) (a : ℕ) (ha : 0 < a) (hal : a < m) :
      (m : ℚ) / (2 : ℚ)^m < (a : ℚ) / (2 : ℚ)^a := by
    rcases a with _ | _ | a
    · omega
    · norm_num at ha
      have h := mono m hm 2 (by omega) (by omega)
      norm_num at h ⊢
      exact h
    · apply mono m hm (a + 2) (by omega) hal
  intro a ha
  by_contra hna
  have hal : a < n := by
    have hne : a ≠ n := by
      intro heq
      exact hnot (heq ▸ ha)
    omega
  have hlt : (n : ℚ) / (2 : ℚ)^n < (a : ℚ) / (2 : ℚ)^a :=
    lower n hn a (hpos a ha) hal
  have hnonneg : ∀ b ∈ S, 0 ≤ (b : ℚ) / (2 : ℚ)^b := by
    intro b hb
    have hb0 : (0 : ℚ) ≤ b := by exact_mod_cast (Nat.zero_le b)
    have hp : (0 : ℚ) < (2 : ℚ)^b := by positivity
    exact div_nonneg hb0 (le_of_lt hp)
  have hsum : (a : ℚ) / (2 : ℚ)^a ≤
      ∑ b ∈ S, (b : ℚ) / (2 : ℚ)^b :=
    Finset.single_le_sum hnonneg ha
  rw [← hrep] at hsum
  linarith

end MathlibPlus.NumberTheory
