import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Data.Fintype.Prod

open scoped BigOperators
open MvPolynomial

namespace MathlibPlus.Algebra.Claim46575

private noncomputable def pairSet (t : ℕ) : Finset (Fin t × Fin t) :=
  Finset.univ.filter (fun p => p.1 < p.2)

private noncomputable def liftIndex {t : ℕ} (ht : 1 ≤ t) (i : Fin (t - 1)) : Fin t :=
  ⟨i.1 + 1, by omega⟩

private noncomputable def intervalSet (t : ℕ) : Finset (Fin (t - 1) × Fin (t - 1)) :=
  Finset.univ.filter (fun p => p.1 < p.2)

noncomputable def F (t : ℕ) (ht : 1 ≤ t) : MvPolynomial (Fin t) ℤ :=
  (∏ p ∈ pairSet t, (X p.2 - X p.1)) *
    (∏ p ∈ intervalSet t,
      ∑ k ∈ Finset.Icc (liftIndex ht p.1) (liftIndex ht p.2), X k)

private lemma card_pairSet (t : ℕ) : (pairSet t).card = t.choose 2 := by
  classical
  simpa [pairSet] using (Fintype.card_product_filter_lt (α := Fin t))

private lemma card_intervalSet (t : ℕ) : (intervalSet t).card = (t - 1).choose 2 := by
  classical
  simpa [intervalSet] using (Fintype.card_product_filter_lt (α := Fin (t - 1)))

private lemma pair_homogeneous {t : ℕ} (p : Fin t × Fin t) :
    (X p.2 - X p.1 : MvPolynomial (Fin t) ℤ).IsHomogeneous 1 := by
  exact (isHomogeneous_X ℤ p.2).sub (isHomogeneous_X ℤ p.1)

private lemma interval_homogeneous {t : ℕ} (ht : 1 ≤ t)
    (p : Fin (t - 1) × Fin (t - 1)) :
    (∑ k ∈ Finset.Icc (liftIndex ht p.1) (liftIndex ht p.2),
      X k : MvPolynomial (Fin t) ℤ).IsHomogeneous 1 := by
  apply IsHomogeneous.sum
  intro k hk
  exact isHomogeneous_X ℤ k

private lemma pair_prod_homogeneous (t : ℕ) :
    (∏ p ∈ pairSet t, (X p.2 - X p.1) : MvPolynomial (Fin t) ℤ).IsHomogeneous (t.choose 2) := by
  classical
  rw [show t.choose 2 = ∑ _p ∈ pairSet t, 1 by
    simp [card_pairSet]]
  apply IsHomogeneous.prod
  intro p hp
  exact pair_homogeneous p

private lemma interval_prod_homogeneous {t : ℕ} (ht : 1 ≤ t) :
    (∏ p ∈ intervalSet t,
      ∑ k ∈ Finset.Icc (liftIndex ht p.1) (liftIndex ht p.2),
        X k : MvPolynomial (Fin t) ℤ).IsHomogeneous ((t - 1).choose 2) := by
  classical
  rw [show (t - 1).choose 2 = ∑ _p ∈ intervalSet t, 1 by
    simp [card_intervalSet]]
  apply IsHomogeneous.prod
  intro p hp
  exact interval_homogeneous ht p

private lemma pair_factor_ne_zero {t : ℕ} {p : Fin t × Fin t}
    (hp : p ∈ pairSet t) :
    (X p.2 - X p.1 : MvPolynomial (Fin t) ℤ) ≠ 0 := by
  have hlt : p.1 < p.2 := by simpa [pairSet] using hp
  have hne : p.1 ≠ p.2 := ne_of_lt hlt
  have hsneq : Finsupp.single p.1 (1 : ℕ) ≠ Finsupp.single p.2 1 := by
    intro h
    exact hne ((Finsupp.single_left_injective (M := ℕ) one_ne_zero) h)
  intro hzero
  have hc := congrArg (fun q : MvPolynomial (Fin t) ℤ =>
      q.coeff (Finsupp.single p.2 1)) hzero
  simp [MvPolynomial.coeff_sub, MvPolynomial.coeff_X, hsneq] at hc

private lemma interval_factor_ne_zero {t : ℕ} {ht : 1 ≤ t}
    {p : Fin (t - 1) × Fin (t - 1)} (hp : p ∈ intervalSet t) :
    (∑ k ∈ Finset.Icc (liftIndex ht p.1) (liftIndex ht p.2),
      X k : MvPolynomial (Fin t) ℤ) ≠ 0 := by
  have hlt : p.1 < p.2 := by simpa [intervalSet] using hp
  intro hzero
  have hc := congrArg (fun q : MvPolynomial (Fin t) ℤ =>
      q.coeff (Finsupp.single (liftIndex ht p.1) 1)) hzero
  have hmem : liftIndex ht p.1 ∈ Finset.Icc (liftIndex ht p.1) (liftIndex ht p.2) := by
    have hle : liftIndex ht p.1 ≤ liftIndex ht p.2 := by
      apply Fin.mk_le_mk.mpr
      omega
    rw [Finset.mem_Icc]
    exact ⟨le_rfl, hle⟩
  have hcoeff :
      (∑ k ∈ Finset.Icc (liftIndex ht p.1) (liftIndex ht p.2),
        if Finsupp.single k (1 : ℕ) =
            Finsupp.single (liftIndex ht p.1) 1 then 1 else 0) = 0 := by
    simpa [MvPolynomial.coeff_sum, MvPolynomial.coeff_X] using hc
  have hsum :
      (∑ k ∈ Finset.Icc (liftIndex ht p.1) (liftIndex ht p.2),
        if Finsupp.single k (1 : ℕ) =
            Finsupp.single (liftIndex ht p.1) 1 then 1 else 0) = 1 := by
    rw [Finset.sum_eq_single (liftIndex ht p.1)]
    · simp
    · intro b hb hba
      have hne : Finsupp.single b (1 : ℕ) ≠
          Finsupp.single (liftIndex ht p.1) 1 := by
        intro h
        exact hba ((Finsupp.single_left_injective (M := ℕ) one_ne_zero) h)
      simp [hne]
    · intro hnot
      exact (hnot hmem).elim
  omega

private lemma F_ne_zero {t : ℕ} (ht : 1 ≤ t) : F t ht ≠ 0 := by
  classical
  dsimp [F]
  apply mul_ne_zero
  · rw [Finset.prod_ne_zero_iff]
    intro p hp
    exact pair_factor_ne_zero hp
  · rw [Finset.prod_ne_zero_iff]
    intro p hp
    exact interval_factor_ne_zero hp

theorem homogeneous_F_claim46575 {t : ℕ} (ht : 1 ≤ t) :
    (F t ht).IsHomogeneous ((t - 1)^2) ∧
      (F t ht).totalDegree = (t - 1)^2 := by
  have hhom : (F t ht).IsHomogeneous ((t - 1)^2) := by
    dsimp [F]
    rw [show (t - 1)^2 = t.choose 2 + (t - 1).choose 2 by
      rw [Nat.choose_two_right, Nat.choose_two_right]
      have h₁ : 2 ∣ t * (t - 1) := Nat.two_dvd_mul_sub_one t
      have h₂ : 2 ∣ (t - 1) * ((t - 1) - 1) :=
        Nat.two_dvd_mul_sub_one (t - 1)
      have e₁ := Nat.div_mul_cancel h₁
      have e₂ := Nat.div_mul_cancel h₂
      rcases eq_or_lt_of_le (show 1 ≤ t by exact ht) with hsmall | hbig
      · have : t = 1 := by omega
        subst t
        norm_num
      · have hsub₁ : t - 1 + 1 = t := Nat.sub_add_cancel ht
        have hsub₂ : t - 1 - 1 + 1 = t - 1 :=
          Nat.sub_add_cancel (by omega)
        nlinarith]
    exact (pair_prod_homogeneous t).mul (interval_prod_homogeneous ht)
  exact ⟨hhom, hhom.totalDegree (F_ne_zero ht)⟩

end MathlibPlus.Algebra.Claim46575
