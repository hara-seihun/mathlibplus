import Mathlib

open scoped BigOperators

namespace MathlibPlus.NumberTheory

/--
The binary-support form of the dyadic valuation sum in admitted claim 51895.
Here `padicValNat 2` is the usual `v₂`, and `bitIndices q` is the finite
support of the binary expansion of `q`.
-/
theorem dyadicValuationSum_claim51895 (q : ℕ) (A : ℤ) :
    let V : ℕ → ℕ := fun q => ∑ r ∈ Finset.range q, 2 ^ padicValNat 2 (r + 1)
    let F : ℕ → ℕ := fun q => (q.bitIndices.map (fun i => (i + 2) * 2 ^ i)).sum
    (2 * V q = F q) ∧
      (A * (q : ℤ) - 2 * (V q : ℤ) =
        (q.bitIndices.map (fun (i : ℕ) =>
          (A - ((i : ℤ) + 2)) * (2 : ℤ) ^ i)).sum) := by
  dsimp
  let V : ℕ → ℕ := fun q => ∑ r ∈ Finset.range q, 2 ^ padicValNat 2 (r + 1)
  let F : ℕ → ℕ := fun q => (q.bitIndices.map (fun i => (i + 2) * 2 ^ i)).sum
  have hodd : ∀ n : ℕ, 2 ^ padicValNat 2 (2 * n + 1) = 1 := by
    intro n
    have hnd : ¬ 2 ∣ 2 * n + 1 := by omega
    rw [padicValNat.eq_zero_of_not_dvd hnd]
    simp
  have heven : ∀ n : ℕ, 2 ^ padicValNat 2 (2 * (n + 1)) =
      2 * (2 ^ padicValNat 2 (n + 1)) := by
    intro n
    rw [padicValNat_base_mul (by omega : 1 < 2) (by omega : n + 1 ≠ 0)]
    rw [pow_add]
    simp [Nat.mul_comm]
  have hV_even : ∀ n : ℕ, V (2 * n) = n + 2 * V n := by
    intro n
    induction n with
    | zero => simp [V]
    | succ n ih =>
      calc
        V (2 * n.succ) = V (2 * n + 1) +
            2 ^ padicValNat 2 (2 * n + 1 + 1) := by
          simp only [V]
          rw [show 2 * n.succ = (2 * n + 1) + 1 by omega]
          rw [Finset.sum_range_succ]
        _ = V (2 * n) + 2 ^ padicValNat 2 (2 * n + 1) +
            2 ^ padicValNat 2 (2 * n + 1 + 1) := by
          congr 1
          simp only [V]
          rw [Finset.sum_range_succ]
        _ = n.succ + 2 * V n.succ := by
          rw [hodd n, show 2 * n + 1 + 1 = 2 * (n + 1) by omega, heven n]
          rw [show V n.succ = V n + 2 ^ padicValNat 2 (n + 1) by
            simp only [V]
            rw [Finset.sum_range_succ]]
          omega
  have hV_odd : ∀ n : ℕ, V (2 * n + 1) = n + 1 + 2 * V n := by
    intro n
    calc
      V (2 * n + 1) = V (2 * n) + 2 ^ padicValNat 2 (2 * n + 1) := by
        simp only [V]
        rw [Finset.sum_range_succ]
      _ = n + 1 + 2 * V n := by rw [hV_even n, hodd n]; omega
  have hmap (L : List ℕ) :
      (L.map (fun x => ((x + 1) + 2) * 2 ^ (x + 1))).sum =
        2 * (L.map (fun x => (x + 2) * 2 ^ x)).sum +
          2 * (L.map (fun x => 2 ^ x)).sum := by
    induction L with
    | nil => simp
    | cons a L ih =>
        simp only [List.map_cons, List.sum_cons]
        rw [ih]
        simp only [pow_succ]
        ring
  have hF_even : ∀ n : ℕ, F (2 * n) = 2 * F n + 2 * n := by
    intro n
    simp only [F, Nat.bitIndices_two_mul, List.map_map]
    calc
      (List.map ((fun i => (i + 2) * 2 ^ i) ∘ fun x => x + 1) n.bitIndices).sum =
          2 * (n.bitIndices.map (fun x => (x + 2) * 2 ^ x)).sum +
            2 * (n.bitIndices.map (fun x => 2 ^ x)).sum := by
        simpa [Function.comp_def, add_assoc] using hmap n.bitIndices
      _ = 2 * (n.bitIndices.map (fun x => (x + 2) * 2 ^ x)).sum + 2 * n := by
        rw [Nat.sum_map_two_pow_bitIndices]
  have hF_odd : ∀ n : ℕ, F (2 * n + 1) = 2 * F n + 2 * n + 2 := by
    intro n
    simp only [F, Nat.bitIndices_two_mul_add_one, List.map_cons, List.sum_cons, Nat.zero_add]
    norm_num
    calc
      2 + (List.map ((fun i => (i + 2) * 2 ^ i) ∘ fun x => x + 1) n.bitIndices).sum =
          2 + (2 * (n.bitIndices.map (fun x => (x + 2) * 2 ^ x)).sum +
            2 * (n.bitIndices.map (fun x => 2 ^ x)).sum) := by
        congr 1
        simpa [Function.comp_def, add_assoc] using hmap n.bitIndices
      _ = 2 * (n.bitIndices.map (fun x => (x + 2) * 2 ^ x)).sum + 2 * n + 2 := by
        rw [Nat.sum_map_two_pow_bitIndices]
        omega
  have hVF : 2 * V q = F q := by
    induction q using Nat.binaryRec with
    | zero => simp [V, F]
    | bit b n ih =>
      cases b with
      | false =>
        rw [show Nat.bit false n = 2 * n by rfl, hV_even n, hF_even n]
        omega
      | true =>
        rw [show Nat.bit true n = 2 * n + 1 by rfl, hV_odd n, hF_odd n]
        omega
  constructor
  · exact hVF
  · change A * (q : ℤ) - 2 * (V q : ℤ) =
        (q.bitIndices.map (fun (i : ℕ) =>
          (A - ((i : ℤ) + 2)) * (2 : ℤ) ^ i)).sum
    have hq : (q.bitIndices.map (fun (i : ℕ) => (2 : ℤ) ^ i)).sum = (q : ℤ) := by
      calc
        (q.bitIndices.map (fun (i : ℕ) => (2 : ℤ) ^ i)).sum =
            ((q.bitIndices.map (fun (i : ℕ) => (2 ^ i : ℕ))).sum : ℤ) := by
          simpa [Function.comp_def, Nat.cast_pow] using
            (List.sum_map_hom q.bitIndices (fun (i : ℕ) => (2 ^ i : ℕ))
              (Nat.castAddMonoidHom ℤ))
        _ = (q : ℤ) := by
          exact congrArg (fun n : ℕ => (n : ℤ))
            (Nat.sum_map_two_pow_bitIndices q)
    have hFcast : (F q : ℤ) =
        (q.bitIndices.map (fun (i : ℕ) =>
          ((i : ℤ) + 2) * (2 : ℤ) ^ i)).sum := by
      dsimp [F]
      symm
      simpa [Function.comp_def, Nat.cast_add, Nat.cast_mul, Nat.cast_pow] using
        (List.sum_map_hom q.bitIndices (fun (i : ℕ) => (i + 2) * 2 ^ i)
          (Nat.castAddMonoidHom ℤ))
    have hG :
        (q.bitIndices.map (fun (i : ℕ) =>
          (A - ((i : ℤ) + 2)) * (2 : ℤ) ^ i)).sum =
          A * (q.bitIndices.map (fun (i : ℕ) => (2 : ℤ) ^ i)).sum -
            (q.bitIndices.map (fun (i : ℕ) =>
              ((i : ℤ) + 2) * (2 : ℤ) ^ i)).sum := by
      induction q.bitIndices with
      | nil => simp
      | cons i l ih =>
          simp only [List.map_cons, List.sum_cons]
          rw [ih]
          ring
    have hVFz : (2 * V q : ℤ) = (F q : ℤ) := by
      exact_mod_cast hVF
    rw [hG, hq, ← hFcast, hVFz]

end MathlibPlus.NumberTheory
