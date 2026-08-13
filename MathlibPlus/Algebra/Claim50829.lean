import Mathlib

namespace MathlibPlus.Algebra.Claim50829

/-- The affine formulas in the repeated-second-branch part of claim 50829 are
pure ring identities; the state-domain and branch-admissibility conditions are
not needed for this algebraic core. -/
theorem second_branch_iterate_claim50829
    {R : Type*} [CommRing R] (x y : R) (X Y : ℕ → R)
    (hX : X 0 = x) (hY : Y 0 = y)
    (r : ℕ)
    (hstepX : ∀ n, n < r → X (n + 1) = 2 * X n)
    (hstepY : ∀ n, n < r → Y (n + 1) = Y n - X n + 1) :
    X r = (2 : R) ^ r * x ∧
      Y r = y - ((2 : R) ^ r - 1) * x + (r : R) := by
  induction r with
  | zero =>
      simp [hX, hY]
  | succ r ihr =>
      have hXr := hstepX r (Nat.lt_succ_self r)
      have hYr := hstepY r (Nat.lt_succ_self r)
      rw [hXr, hYr]
      have hprevX : ∀ n, n < r → X (n + 1) = 2 * X n :=
        fun n hn => hstepX n (Nat.lt_succ_of_lt hn)
      have hprevY : ∀ n, n < r → Y (n + 1) = Y n - X n + 1 :=
        fun n hn => hstepY n (Nat.lt_succ_of_lt hn)
      have hi := ihr hprevX hprevY
      rw [hi.1, hi.2]
      constructor
      · rw [pow_succ]
        ring
      · rw [pow_succ]
        norm_num [Nat.cast_add]
        ring

/-- The affine formulas in the repeated-first-branch part of claim 50829 are
pure ring identities; the state-domain and branch-admissibility conditions are
not needed for this algebraic core. -/
theorem first_branch_iterate_claim50829
    {R : Type*} [CommRing R] (x y : R) (X Y : ℕ → R)
    (hX : X 0 = x) (hY : Y 0 = y)
    (r : ℕ)
    (hstepY : ∀ n, n < r → Y (n + 1) = 2 * Y n)
    (hstepX : ∀ n, n < r → X (n + 1) = X n - Y n + 1) :
    Y r = (2 : R) ^ r * y ∧
      X r = x - ((2 : R) ^ r - 1) * y + (r : R) := by
  induction r with
  | zero =>
      simp [hX, hY]
  | succ r ihr =>
      have hYr := hstepY r (Nat.lt_succ_self r)
      have hXr := hstepX r (Nat.lt_succ_self r)
      rw [hYr, hXr]
      have hprevY : ∀ n, n < r → Y (n + 1) = 2 * Y n :=
        fun n hn => hstepY n (Nat.lt_succ_of_lt hn)
      have hprevX : ∀ n, n < r → X (n + 1) = X n - Y n + 1 :=
        fun n hn => hstepX n (Nat.lt_succ_of_lt hn)
      have hi := ihr hprevY hprevX
      rw [hi.1, hi.2]
      constructor
      · rw [pow_succ]
        ring
      · rw [pow_succ]
        norm_num [Nat.cast_add]
        ring

end MathlibPlus.Algebra.Claim50829
