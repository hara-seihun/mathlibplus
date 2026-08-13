import Mathlib

namespace MathlibPlus.LinearAlgebra

private def pairProduct (m : ℕ) (q : ℝ) : ℝ :=
  ∏ i ∈ Finset.range m, ∏ j ∈ Finset.range m,
    if i < j then q ^ j - q ^ i else 1

private def factorProduct (m : ℕ) (q : ℝ) : ℝ :=
  q ^ Nat.choose m 3 *
    ∏ d ∈ Finset.range m,
      (q ^ (d + 1) - 1) ^ (m - (d + 1))

private lemma pairProduct_succ (m : ℕ) (q : ℝ) :
    pairProduct (m + 1) q =
      pairProduct m q * ∏ i ∈ Finset.range m, (q ^ m - q ^ i) := by
  unfold pairProduct
  rw [Finset.prod_range_succ]
  have hlast :
      (∏ j ∈ Finset.range (m + 1), if m < j then q ^ j - q ^ m else 1) = 1 := by
    apply Finset.prod_eq_one
    intro j hj
    simp only [Finset.mem_range] at hj
    simp [Nat.not_lt_of_ge (Nat.le_of_lt_succ hj)]
  rw [hlast, mul_one]
  calc
    (∏ x ∈ Finset.range m, ∏ j ∈ Finset.range (m + 1),
        if x < j then q ^ j - q ^ x else 1) =
        ∏ x ∈ Finset.range m,
          ((∏ j ∈ Finset.range m, if x < j then q ^ j - q ^ x else 1) *
            (q ^ m - q ^ x)) := by
      apply Finset.prod_congr rfl
      intro x hx
      rw [Finset.prod_range_succ]
      simp only [Finset.mem_range] at hx
      rw [if_pos hx]
    _ = (∏ x ∈ Finset.range m, ∏ j ∈ Finset.range m,
          if x < j then q ^ j - q ^ x else 1) *
        ∏ x ∈ Finset.range m, (q ^ m - q ^ x) := by
      rw [Finset.prod_mul_distrib]

private lemma reverseFactors (m : ℕ) (q : ℝ) :
    ∏ i ∈ Finset.range m, (q ^ (m - i) - 1) =
      ∏ d ∈ Finset.range m, (q ^ (d + 1) - 1) := by
  cases m with
  | zero => simp
  | succ k =>
    calc
      (∏ i ∈ Finset.range (k + 1), (q ^ (k + 1 - i) - 1)) =
          ∏ i ∈ Finset.range (k + 1),
            (q ^ ((k - i) + 1) - 1) := by
        apply Finset.prod_congr rfl
        intro i hi
        have hil : i < k + 1 := Finset.mem_range.mp hi
        congr 2
        omega
      _ = ∏ i ∈ Finset.range (k + 1), (q ^ (i + 1) - 1) := by
        exact Finset.prod_range_reflect (fun i => q ^ (i + 1) - 1) (k + 1)

private lemma newFactor (m : ℕ) (q : ℝ) :
    ∏ i ∈ Finset.range m, (q ^ m - q ^ i) =
      q ^ Nat.choose m 2 * ∏ i ∈ Finset.range m, (q ^ (m - i) - 1) := by
  calc
    (∏ i ∈ Finset.range m, (q ^ m - q ^ i)) =
        ∏ i ∈ Finset.range m, (q ^ i * (q ^ (m - i) - 1)) := by
      apply Finset.prod_congr rfl
      intro i hi
      have him : i ≤ m := (Finset.mem_range.mp hi).le
      have hsum : i + (m - i) = m := Nat.add_sub_of_le him
      have hp : q ^ m = q ^ i * q ^ (m - i) := by
        rw [← pow_add, hsum]
      rw [hp]
      ring
    _ = (∏ i ∈ Finset.range m, q ^ i) *
        ∏ i ∈ Finset.range m, (q ^ (m - i) - 1) := by
      rw [Finset.prod_mul_distrib]
    _ = q ^ Nat.choose m 2 *
        ∏ i ∈ Finset.range m, (q ^ (m - i) - 1) := by
      rw [Finset.prod_pow_eq_pow_sum, Finset.sum_range_id, Nat.choose_two_right]

private lemma factorProduct_succ (m : ℕ) (q : ℝ) :
    factorProduct (m + 1) q =
      factorProduct m q * ∏ i ∈ Finset.range m, (q ^ m - q ^ i) := by
  unfold factorProduct
  rw [newFactor, reverseFactors]
  have hpow :
      (∏ d ∈ Finset.range m, (q ^ (d + 1) - 1) ^ (m - (d + 1))) *
          ∏ d ∈ Finset.range m, (q ^ (d + 1) - 1) =
        ∏ d ∈ Finset.range m, (q ^ (d + 1) - 1) ^ (m - d) := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro d hd
    calc
      (q ^ (d + 1) - 1) ^ (m - (d + 1)) * (q ^ (d + 1) - 1) =
          (q ^ (d + 1) - 1) ^ (m - (d + 1)) *
            (q ^ (d + 1) - 1) ^ 1 := by rw [pow_one]
      _ = (q ^ (d + 1) - 1) ^ (m - (d + 1) + 1) := by
        exact (pow_add (q ^ (d + 1) - 1) (m - (d + 1)) 1).symm
      _ = (q ^ (d + 1) - 1) ^ (m - d) := by
        have hdm : d < m := Finset.mem_range.mp hd
        congr 2
        omega
  have hlast :
      ∏ d ∈ Finset.range (m + 1),
          (q ^ (d + 1) - 1) ^ ((m + 1) - (d + 1)) =
        ∏ d ∈ Finset.range m, (q ^ (d + 1) - 1) ^ (m - d) := by
    rw [Finset.prod_range_succ]
    simp only [Nat.sub_self, pow_zero, mul_one]
    apply Finset.prod_congr rfl
    intro d hd
    congr 1
    simpa only [Nat.succ_sub_succ_eq_sub]
  rw [hlast]
  have hchoose : Nat.choose (m + 1) 3 = Nat.choose m 2 + Nat.choose m 3 := by
    simpa [Nat.succ_eq_add_one, Nat.add_comm] using Nat.choose_succ_succ m 2
  rw [hchoose, pow_add, ← hpow]
  ring

private lemma pairProduct_factor (m : ℕ) (q : ℝ) :
    pairProduct m q = factorProduct m q := by
  induction m with
  | zero => simp [pairProduct, factorProduct]
  | succ m ih =>
    rw [pairProduct_succ, factorProduct_succ, ih]

private lemma pairProduct_as_fin (m : ℕ) (q : ℝ) :
    (∏ i : Fin m, ∏ j ∈ Finset.Ioi i, (q ^ j.1 - q ^ i.1)) = pairProduct m q := by
  classical
  have inner (i : Fin m) :
      (∏ j ∈ Finset.Ioi i, (q ^ j.1 - q ^ i.1)) =
        ∏ j : Fin m, if i < j then q ^ j.1 - q ^ i.1 else 1 := by
    rw [← Finset.prod_filter]
    rw [Finset.filter_lt_eq_Ioi]
  rw [show (∏ i : Fin m, ∏ j ∈ Finset.Ioi i, (q ^ j.1 - q ^ i.1)) =
      ∏ i : Fin m, ∏ j : Fin m, if i < j then q ^ j.1 - q ^ i.1 else 1 by
        apply Finset.prod_congr rfl
        intro i hi
        exact inner i]
  simp only [Finset.prod_fin_eq_prod_range]
  apply Finset.prod_congr rfl
  intro x hx
  have hxlt : x < m := Finset.mem_range.mp hx
  simp only [hxlt, if_pos]
  apply Finset.prod_congr rfl
  intro y hy
  have hylt : y < m := Finset.mem_range.mp hy
  simp only [hylt, if_pos]
  rfl

private lemma determinant_eq_finProduct (m : ℕ) (q : ℝ) :
    (Matrix.of fun r s : Fin m => q ^ (r.1 * s.1)).det =
      ∏ i : Fin m, ∏ j ∈ Finset.Ioi i, (q ^ j.1 - q ^ i.1) := by
  calc
    (Matrix.of fun r s : Fin m => q ^ (r.1 * s.1)).det =
        (Matrix.vandermonde (fun i : Fin m => q ^ i.1)).transpose.det := by
      congr 1
      funext r s
      simp only [Matrix.transpose_apply, Matrix.vandermonde_apply]
      rw [← pow_mul]
      exact congrArg (fun e : ℕ => q ^ e) (Nat.mul_comm r.1 s.1)
    _ = (Matrix.vandermonde (fun i : Fin m => q ^ i.1)).det :=
      Matrix.det_transpose _
    _ = ∏ i : Fin m, ∏ j ∈ Finset.Ioi i, (q ^ j.1 - q ^ i.1) := by
      simpa using (Matrix.det_vandermonde (fun i : Fin m => q ^ i.1))

private lemma factorRange_source (m : ℕ) (q : ℝ) :
    ∏ d ∈ Finset.range m, (q ^ (d + 1) - 1) ^ (m - (d + 1)) =
      ∏ d ∈ Finset.range (m - 1), (q ^ (d + 1) - 1) ^ (m - (d + 1)) := by
  cases m with
  | zero => simp
  | succ k =>
    simp only [Nat.succ_sub_one]
    rw [Finset.prod_range_succ]
    simp

private theorem exact_lattice_heat (q : ℝ) (hq : 1 < q) (m : ℕ) :
    let H : Matrix (Fin m) (Fin m) ℝ :=
      Matrix.of fun r s => q ^ (r.1 * s.1)
    H.det = ∏ i : Fin m, ∏ j ∈ Finset.Ioi i, (q ^ j.1 - q ^ i.1) ∧
    H.det = q ^ Nat.choose m 3 *
      ∏ d ∈ Finset.range (m - 1), (q ^ (d + 1) - 1) ^ (m - (d + 1)) ∧
    0 < H.det := by
  dsimp
  have hdet := determinant_eq_finProduct m q
  have hfactor := pairProduct_factor m q
  have hsource := factorRange_source m q
  have hdetfactor :
      (Matrix.of fun r s : Fin m => q ^ (r.1 * s.1)).det =
        q ^ Nat.choose m 3 *
          ∏ d ∈ Finset.range (m - 1), (q ^ (d + 1) - 1) ^ (m - (d + 1)) := by
    calc
      (Matrix.of fun r s : Fin m => q ^ (r.1 * s.1)).det = pairProduct m q :=
        hdet.trans (pairProduct_as_fin m q)
      _ = factorProduct m q := hfactor
      _ = q ^ Nat.choose m 3 *
          ∏ d ∈ Finset.range m, (q ^ (d + 1) - 1) ^ (m - (d + 1)) := rfl
      _ = q ^ Nat.choose m 3 *
          ∏ d ∈ Finset.range (m - 1), (q ^ (d + 1) - 1) ^ (m - (d + 1)) := by
        rw [hsource]
  have hfactorpos : 0 < factorProduct m q := by
    unfold factorProduct
    apply mul_pos
    · exact pow_pos (by linarith : 0 < q) _
    · apply Finset.prod_pos
      intro d hd
      apply pow_pos
      apply sub_pos.mpr
      exact one_lt_pow₀ hq (Nat.succ_ne_zero d)
  have hdetpos : 0 < (Matrix.of fun r s : Fin m => q ^ (r.1 * s.1)).det := by
    rw [hdet.trans (pairProduct_as_fin m q), hfactor]
    exact hfactorpos
  exact ⟨hdet, hdetfactor, hdetpos⟩

/-- Exact determinant, q-factorization, and positivity for the lattice heat matrix in claim 9054. -/
theorem latticeHeatCasoratian_claim9054 (γ : ℝ) (n m : ℕ)
    (hγ : 0 < γ) (hn : 0 < n) :
    let q : ℝ := Real.exp (2 * γ / (n : ℝ))
    let H : Matrix (Fin m) (Fin m) ℝ :=
      Matrix.of fun r s => q ^ (r.1 * s.1)
    1 < q ∧
    H.det = ∏ i : Fin m, ∏ j ∈ Finset.Ioi i, (q ^ j.1 - q ^ i.1) ∧
    H.det = q ^ Nat.choose m 3 *
      ∏ d ∈ Finset.range (m - 1), (q ^ (d + 1) - 1) ^ (m - (d + 1)) ∧
    0 < H.det := by
  dsimp
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have harg : 0 < 2 * γ / (n : ℝ) := by positivity
  have hq : 1 < Real.exp (2 * γ / (n : ℝ)) :=
    Real.one_lt_exp_iff.mpr harg
  exact ⟨hq, exact_lattice_heat _ hq m⟩

end MathlibPlus.LinearAlgebra
