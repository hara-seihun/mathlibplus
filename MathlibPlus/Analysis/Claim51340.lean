import Mathlib

namespace MathlibPlus.Analysis.Claim51340

open scoped BigOperators

/-- The scheduling bounds from the S6 portion of claim 51340.

The source defines `L`, `V`, `W`, and `S` from the finite coefficient list and
uses the descending rank of a positive coefficient.  The transcript-specific
quantities `Psi` and `R` are not defined in the claim itself, so this theorem
retains exactly the stated finite scheduling core rather than inventing their
carrier interfaces.
-/
theorem schedulingInequalities_claim51340
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (α : ι → ℝ) (Q L V W S : ℝ) (r : ι → ℕ)
    (hα0 : ∀ i, 0 ≤ α i)
    (hα1 : ∀ i, α i ≤ 1)
    (hL : (∑ i, α i) = L)
    (hV : V = ∑ i, α i ^ 2)
    (hW : W = ∑ i, α i ^ 2 * (1 - α i))
    (hS : S = ∑ i, (r i : ℝ) * α i ^ 2 * (1 - α i))
    (hL1 : L ≤ 1)
    (hQ : L ≤ Q)
    (hrank : ∀ i, 0 < α i →
      r i = (Finset.univ.filter (fun j => α i ≤ α j)).card) :
    W ≤ 1 - V ∧ S ≤ Q * (1 - V) := by
  have hL0 : 0 ≤ L := by
    rw [← hL]
    exact Finset.sum_nonneg (fun i _ => hα0 i)

  have hpoint : ∀ i, α i ^ 2 * (2 - α i) ≤ α i := by
    intro i
    have hnonneg : 0 ≤ α i * (1 - α i) ^ 2 :=
      mul_nonneg (hα0 i) (sq_nonneg (1 - α i))
    nlinarith

  have hVplusW : V + W ≤ L := by
    calc
      V + W = (∑ i, α i ^ 2) + (∑ i, α i ^ 2 * (1 - α i)) := by
        rw [hV, hW]
      _ = ∑ i, (α i ^ 2 + α i ^ 2 * (1 - α i)) := by
        rw [Finset.sum_add_distrib]
      _ = ∑ i, α i ^ 2 * (2 - α i) := by
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ ≤ ∑ i, α i := by
        exact Finset.sum_le_sum (fun i hi => hpoint i)
      _ = L := hL

  have hW_le : W ≤ 1 - V := by
    nlinarith [hVplusW, hL1]

  have hfiltered_le (i : ι) :
      (∑ j ∈ Finset.univ.filter (fun j => α i ≤ α j), α j) ≤ L := by
    calc
      (∑ j ∈ Finset.univ.filter (fun j => α i ≤ α j), α j) ≤
          ∑ j ∈ (Finset.univ : Finset ι), α j := by
        exact Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.filter_subset _ _)
          (fun j hj hnot => hα0 j)
      _ = L := hL

  have hrank_le (i : ι) : (r i : ℝ) * α i ≤ L := by
    by_cases hi : 0 < α i
    · let t := Finset.univ.filter (fun j => α i ≤ α j)
      have hri : r i = t.card := hrank i hi
      have hcard : (t.card : ℝ) * α i = ∑ j ∈ t, α i := by
        calc
          (t.card : ℝ) * α i = t.card • α i := by
            simp [nsmul_eq_mul]
          _ = ∑ j ∈ t, α i := by
            symm
            exact Finset.sum_const (s := t) (α i)
      calc
        (r i : ℝ) * α i = (t.card : ℝ) * α i := by rw [hri]
        _ = ∑ j ∈ t, α i := hcard
        _ ≤ ∑ j ∈ t, α j := by
          exact Finset.sum_le_sum (fun j hj => (Finset.mem_filter.mp hj).2)
        _ ≤ L := hfiltered_le i
    · have hai : α i = 0 := le_antisymm (le_of_not_gt hi) (hα0 i)
      rw [hai]
      simpa using hL0

  have hbeta_nonneg (i : ι) : 0 ≤ α i * (1 - α i) :=
    mul_nonneg (hα0 i) (sub_nonneg.mpr (hα1 i))

  have hterm (i : ι) :
      (r i : ℝ) * α i ^ 2 * (1 - α i) ≤
        L * (α i * (1 - α i)) := by
    calc
      (r i : ℝ) * α i ^ 2 * (1 - α i) =
          ((r i : ℝ) * α i) * (α i * (1 - α i)) := by ring
      _ ≤ L * (α i * (1 - α i)) :=
        mul_le_mul_of_nonneg_right (hrank_le i) (hbeta_nonneg i)

  have hsum_beta : (∑ i, α i * (1 - α i)) = L - V := by
    calc
      (∑ i, α i * (1 - α i)) = ∑ i, (α i - α i ^ 2) := by
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = (∑ i, α i) - (∑ i, α i ^ 2) := by
        rw [Finset.sum_sub_distrib]
      _ = L - V := by rw [hL, ← hV]

  have hLV : 0 ≤ L - V := by
    rw [← hsum_beta]
    exact Finset.sum_nonneg (fun i _ => hbeta_nonneg i)

  have hV1 : V ≤ 1 := by
    have : V ≤ L := sub_nonneg.mp hLV
    exact this.trans hL1

  have hS_le : S ≤ L * (L - V) := by
    calc
      S = ∑ i, (r i : ℝ) * α i ^ 2 * (1 - α i) := hS
      _ ≤ ∑ i, L * (α i * (1 - α i)) :=
        Finset.sum_le_sum (fun i hi => hterm i)
      _ = L * (∑ i, α i * (1 - α i)) := by
        symm
        exact Finset.mul_sum Finset.univ (fun i => α i * (1 - α i)) L
      _ = L * (L - V) := by rw [hsum_beta]

  have hLL : L * (L - V) ≤ L * (1 - V) := by
    exact mul_le_mul_of_nonneg_left (sub_le_sub_right hL1 V) hL0

  have hQmul : L * (1 - V) ≤ Q * (1 - V) := by
    exact mul_le_mul_of_nonneg_right hQ (sub_nonneg.mpr hV1)

  exact ⟨hW_le, hS_le.trans (hLL.trans hQmul)⟩

end MathlibPlus.Analysis.Claim51340
