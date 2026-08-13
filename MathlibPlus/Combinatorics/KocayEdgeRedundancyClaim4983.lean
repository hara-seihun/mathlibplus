import Mathlib

namespace MathlibPlus.Combinatorics

open scoped BigOperators

/-- The total repeated-edge incidence identity for a finite ordered edge cover.

The hypotheses `hsub` and `hcover` are the explicit finite-set content of the
source's `c(F,Y) > 0` cover condition. -/
theorem kocayEdgeRedundancy_claim4983
    {E : Type*} [Fintype E] [DecidableEq E]
    {k m : ℕ} (F : Fin k → Finset E) (Y : Finset E)
    (hm : Y.card = m)
    (hsub : ∀ i, F i ⊆ Y)
    (hcover : ∀ e ∈ Y, ∃ i, e ∈ F i) :
    ((∑ i : Fin k, (F i).card : ℤ) - m : ℤ) =
        ∑ e ∈ Y, ((∑ i : Fin k, if e ∈ F i then (1 : ℤ) else 0) - 1) ∧
      0 ≤ ((∑ i : Fin k, (F i).card : ℤ) - m : ℤ) := by
  have hcard : ∀ i : Fin k,
      ((F i).card : ℤ) = ∑ e ∈ Y, if e ∈ F i then (1 : ℤ) else 0 := by
    intro i
    have hfilter : Y.filter (fun e => e ∈ F i) = F i := by
      ext e
      constructor
      · intro he
        exact (Finset.mem_filter.mp he).2
      · intro he
        exact Finset.mem_filter.mpr ⟨hsub i he, he⟩
    rw [← hfilter]
    rw [Finset.card_filter]
    simp [hsub i]
  have hsum : (∑ i : Fin k, (F i).card : ℤ) =
      ∑ e ∈ Y, (∑ i : Fin k, if e ∈ F i then (1 : ℤ) else 0) := by
    calc
      (∑ i : Fin k, (F i).card : ℤ) =
          ∑ i : Fin k, ∑ e ∈ Y, if e ∈ F i then (1 : ℤ) else 0 := by
            simp_rw [hcard]
      _ = ∑ e ∈ Y, ∑ i : Fin k, if e ∈ F i then (1 : ℤ) else 0 := by
            rw [Finset.sum_comm]
  have hnonneg : ∀ e ∈ Y,
      (0 : ℤ) ≤ (∑ i : Fin k, if e ∈ F i then (1 : ℤ) else 0) - 1 := by
    intro e he
    obtain ⟨i, hi⟩ := hcover e he
    have hone : (1 : ℤ) ≤ ∑ j : Fin k, if e ∈ F j then (1 : ℤ) else 0 := by
      have hterm : (1 : ℤ) ≤ if e ∈ F i then (1 : ℤ) else 0 := by simp [hi]
      have hsum_ge :
          (if e ∈ F i then (1 : ℤ) else 0) ≤
            ∑ j : Fin k, if e ∈ F j then (1 : ℤ) else 0 :=
        Finset.single_le_sum
          (s := (Finset.univ : Finset (Fin k)))
          (f := fun j : Fin k => if e ∈ F j then (1 : ℤ) else 0)
          (fun j _ => by positivity) (Finset.mem_univ i)
      exact le_trans hterm hsum_ge
    omega
  have hmZ : (m : ℤ) = (Y.card : ℤ) := by
    exact_mod_cast hm.symm
  have hcardY : (Y.card : ℤ) = Y.sum (fun _ => (1 : ℤ)) := by
    rw [Finset.card_eq_sum_ones]
    norm_cast
  have hidentity :
      ((∑ i : Fin k, (F i).card : ℤ) - m : ℤ) =
        Y.sum (fun e => (∑ i : Fin k, if e ∈ F i then (1 : ℤ) else 0) - 1) := by
    calc
      ((∑ i : Fin k, (F i).card : ℤ) - m : ℤ) =
          Y.sum (fun e => ∑ i : Fin k, if e ∈ F i then (1 : ℤ) else 0) -
            (Y.card : ℤ) := by rw [hmZ, hsum]
      _ = Y.sum (fun e => ∑ i : Fin k, if e ∈ F i then (1 : ℤ) else 0) -
            Y.sum (fun _ => (1 : ℤ)) := by rw [hcardY]
      _ = Y.sum (fun e => (∑ i : Fin k, if e ∈ F i then (1 : ℤ) else 0) - 1) := by
        rw [Finset.sum_sub_distrib]
  constructor
  · simpa using hidentity
  · rw [hidentity]
    exact Finset.sum_nonneg (by
      intro e he
      exact hnonneg e he)

end MathlibPlus.Combinatorics
