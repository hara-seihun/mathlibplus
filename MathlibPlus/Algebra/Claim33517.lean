import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

open scoped BigOperators

namespace MathlibPlus.Algebra.Claim33517

/-- The two characteristic-two arm identities from claim 33517.

The packet's `F_a` and `J_a` are the exact arm polynomials
`F_a = sum_(k=1)^a (a-k+1)t^k` and `J_a = sum_(k=0)^a t^k` from R-1709.
All natural parity coefficients are cast into `ZMod 2`, so no characteristic or
index convention is hidden in the formal statement. -/
theorem arm_identities_claim33517 (a : ℕ) :
    let F : ℕ → Polynomial (ZMod 2) := fun b =>
      ∑ k ∈ Finset.range b,
        Polynomial.C ((b - k : ℕ) : ZMod 2) * Polynomial.X ^ (k + 1)
    let J : ℕ → Polynomial (ZMod 2) := fun b =>
      ∑ k ∈ Finset.range (b + 1), Polynomial.X ^ k
    ((1 + Polynomial.X) ^ 2 * F a =
        Polynomial.C ((a % 2 : ℕ) : ZMod 2) * Polynomial.X +
          Polynomial.C (((a + 1) % 2 : ℕ) : ZMod 2) * Polynomial.X ^ 2 +
            Polynomial.X ^ (a + 2)) ∧
      ((1 + Polynomial.X) * J a = 1 + Polynomial.X ^ (a + 1)) := by
  classical
  let F : ℕ → Polynomial (ZMod 2) := fun b =>
    ∑ k ∈ Finset.range b,
      Polynomial.C ((b - k : ℕ) : ZMod 2) * Polynomial.X ^ (k + 1)
  let J : ℕ → Polynomial (ZMod 2) := fun b =>
    ∑ k ∈ Finset.range (b + 1), Polynomial.X ^ k
  let R : ℕ → Polynomial (ZMod 2) := fun b =>
    Polynomial.C ((b % 2 : ℕ) : ZMod 2) * Polynomial.X +
      Polynomial.C (((b + 1) % 2 : ℕ) : ZMod 2) * Polynomial.X ^ 2 +
        Polynomial.X ^ (b + 2)
  change ((1 + Polynomial.X) ^ 2 * F a = R a) ∧
    ((1 + Polynomial.X) * J a = 1 + Polynomial.X ^ (a + 1))
  have htwoZ : (2 : ZMod 2) = 0 := by decide
  have htwoPoly : (2 : Polynomial (ZMod 2)) = 0 := by
    ext (_ | i)
    · simp [htwoZ]
    · simp
  have hchar :
      (1 + Polynomial.X : Polynomial (ZMod 2)) ^ 2 = 1 + Polynomial.X ^ 2 := by
    ring_nf <;> simp [htwoPoly]
  have hJ_succ (n : ℕ) : J (n + 1) = J n + Polynomial.X ^ (n + 1) := by
    simp [J, Finset.sum_range_succ, Nat.add_assoc]
  have hJ : ∀ n : ℕ,
      (1 + Polynomial.X) * J n = 1 + Polynomial.X ^ (n + 1) := by
    intro n
    induction n with
    | zero =>
        simp [J]
    | succ n ih =>
        rw [hJ_succ n, mul_add, ih]
        simp only [pow_succ]
        ring_nf <;> simp [htwoPoly]
  have hF_two (n : ℕ) : F (n + 2) = F n + Polynomial.X ^ (n + 2) := by
    change
      (∑ k ∈ Finset.range (n + 2),
          Polynomial.C ((n + 2 - k : ℕ) : ZMod 2) * Polynomial.X ^ (k + 1)) =
        (∑ k ∈ Finset.range n,
          Polynomial.C ((n - k : ℕ) : ZMod 2) * Polynomial.X ^ (k + 1)) +
          Polynomial.X ^ (n + 2)
    have hsum :
        (∑ k ∈ Finset.range n,
          Polynomial.C ((n + 2 - k : ℕ) : ZMod 2) * Polynomial.X ^ (k + 1)) =
          ∑ k ∈ Finset.range n,
            Polynomial.C ((n - k : ℕ) : ZMod 2) * Polynomial.X ^ (k + 1) := by
      apply Finset.sum_congr rfl
      intro k hk
      have hklt : k < n := Finset.mem_range.mp hk
      have hsub : n + 2 - k = n - k + 2 := by omega
      simp [hsub, Nat.cast_add, htwoZ]
    have hone : n + 2 - (n + 1) = 1 := by omega
    have htwo : n + 2 - n = 2 := by omega
    rw [show n + 2 = (n + 1) + 1 by omega]
    simp only [Finset.sum_range_succ]
    rw [hsum, htwo, hone]
    simp [htwoZ, htwoPoly]
  have hF : ∀ n : ℕ, (1 + Polynomial.X) ^ 2 * F n = R n := by
    intro n
    induction n using Nat.twoStepInduction with
    | zero =>
        simp [F, R, hchar, htwoPoly, htwoZ, ← two_mul]
    | one =>
        simp [F, R, hchar, htwoPoly, htwoZ] <;> ring_nf <;>
          simp [htwoPoly, htwoZ]
    | more n ih0 ih1 =>
        rw [hF_two n, mul_add, ih0]
        have hmod0 : (n + 2) % 2 = n % 2 := by omega
        have hmod1 : (n + 2 + 1) % 2 = (n + 1) % 2 := by omega
        have hlast : n + 2 + 2 = n + 4 := by omega
        dsimp [R]
        rw [hmod0, hmod1, hlast, hchar]
        have hpow :
            (Polynomial.X : Polynomial (ZMod 2)) ^ 2 *
                (Polynomial.X : Polynomial (ZMod 2)) ^ (n + 2) =
              (Polynomial.X : Polynomial (ZMod 2)) ^ (n + 4) := by
          rw [← pow_add]
          congr 1 <;> omega
        rw [add_mul, hpow]
        ring_nf <;> simp [htwoPoly, htwoZ]
  exact ⟨hF a, hJ a⟩

end MathlibPlus.Algebra.Claim33517
