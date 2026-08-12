import Mathlib

open scoped BigOperators

namespace MathlibPlus.Combinatorics

private lemma card_unordered_bool_diff (p : ℕ) (b : Fin p → Bool) :
    ((Finset.univ : Finset (Fin p × Fin p)).filter
        (fun x => x.1 < x.2 ∧ b x.1 ≠ b x.2)).card =
      ((Finset.univ : Finset (Fin p)).filter (fun i => b i = true)).card *
        ((Finset.univ : Finset (Fin p)).filter (fun i => b i = false)).card := by
  classical
  let all : Finset (Fin p × Fin p) := Finset.univ ×ˢ Finset.univ
  let trueRows : Finset (Fin p) := Finset.univ.filter (fun i => b i = true)
  let falseRows : Finset (Fin p) := Finset.univ.filter (fun i => b i = false)
  let diff : Finset (Fin p × Fin p) := all.filter (fun x => b x.1 ≠ b x.2)
  let ltDiff : Finset (Fin p × Fin p) :=
    all.filter (fun x => x.1 < x.2 ∧ b x.1 ≠ b x.2)
  let gtDiff : Finset (Fin p × Fin p) :=
    all.filter (fun x => x.2 < x.1 ∧ b x.1 ≠ b x.2)
  have hdiff : diff = ltDiff ∪ gtDiff := by
    ext x
    by_cases h : b x.1 ≠ b x.2
    · have hne : x.1 ≠ x.2 := by
        intro he
        exact h (congrArg b he)
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have hn : ¬ x.2 < x.1 := not_lt_of_ge (le_of_lt hlt)
        simp [all, diff, ltDiff, gtDiff, h, hlt, hn]
      · have hn : ¬ x.1 < x.2 := not_lt_of_ge (le_of_lt hgt)
        simp [all, diff, ltDiff, gtDiff, h, hgt, hn]
    · simp [all, diff, ltDiff, gtDiff, h]
  have hdisj : Disjoint ltDiff gtDiff := by
    rw [Finset.disjoint_left]
    intro x hx hy
    exact (not_lt_of_ge (le_of_lt (Finset.mem_filter.1 hy).2.1)
      (Finset.mem_filter.1 hx).2.1)
  have hswap : ltDiff.image Prod.swap = gtDiff := by
    ext x
    constructor
    · intro hx
      rcases Finset.mem_image.1 hx with ⟨⟨y₁, y₂⟩, hy, rfl⟩
      have hy' := Finset.mem_filter.1 hy
      change (y₂, y₁) ∈ gtDiff
      exact Finset.mem_filter.2 ⟨by simp [all], ⟨hy'.2.1, hy'.2.2.symm⟩⟩
    · intro hx
      rcases x with ⟨x₁, x₂⟩
      have hx' := Finset.mem_filter.1 hx
      refine Finset.mem_image.2 ⟨(x₂, x₁), ?_, ?_⟩
      · exact Finset.mem_filter.2 ⟨by simp [all], ⟨hx'.2.1, hx'.2.2.symm⟩⟩
      · rfl
  have hcard_swap : gtDiff.card = ltDiff.card := by
    rw [← hswap]
    apply Finset.card_image_iff.2
    intro x hx y hy hxy
    rcases x with ⟨x₁, x₂⟩
    rcases y with ⟨y₁, y₂⟩
    simp only [Prod.swap_prod_mk, Prod.mk.injEq] at hxy
    exact Prod.ext hxy.2 hxy.1
  have hcard_diff : diff.card = 2 * (trueRows.card * falseRows.card) := by
    have heq : diff.card = trueRows.card * falseRows.card + falseRows.card * trueRows.card := by
      rw [show diff = all.filter (fun x => (b x.1 = true) = (b x.2 = false)) by
        ext x
        by_cases h₁ : b x.1 <;> by_cases h₂ : b x.2 <;>
          simp [diff, all, h₁, h₂]]
      simpa [diff, all, trueRows, falseRows] using
        (Finset.filter_product_card (s := (Finset.univ : Finset (Fin p)))
          (t := (Finset.univ : Finset (Fin p)))
          (fun i => b i = true) (fun i => b i = false))
    rw [heq]
    ring
  have hcard_partition : diff.card = ltDiff.card + gtDiff.card := by
    rw [hdiff, Finset.card_union_of_disjoint hdisj]
  have hcard_lt : ltDiff.card = trueRows.card * falseRows.card := by
    have htwo : diff.card = 2 * ltDiff.card := by
      rw [hcard_partition, hcard_swap]
      ring
    rw [hcard_diff] at htwo
    omega
  simpa [all, ltDiff, trueRows, falseRows] using hcard_lt

/-- Claim 20434: the total Hamming distance of binary rows over unordered
pairs is the sum, over support columns, of the number of one-rows times the
number of zero-rows. -/
theorem claim20434_binaryColumnPairDistance
    (p n : ℕ) (rows : Fin p → Fin n → Bool) :
    (∑ x ∈ ((Finset.univ : Finset (Fin p × Fin p)).filter
        (fun x => x.1 < x.2)),
      ∑ z : Fin n, if rows x.1 z ≠ rows x.2 z then 1 else 0) =
      ∑ z : Fin n,
        ((Finset.univ : Finset (Fin p)).filter (fun i => rows i z = true)).card *
          (p - ((Finset.univ : Finset (Fin p)).filter (fun i => rows i z = true)).card) := by
  classical
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z hz
  let b : Fin p → Bool := fun i => rows i z
  let pairs : Finset (Fin p × Fin p) :=
    (Finset.univ ×ˢ Finset.univ).filter (fun x => x.1 < x.2)
  have hsum :
      (∑ x ∈ pairs, if b x.1 ≠ b x.2 then 1 else 0) =
        ((Finset.univ : Finset (Fin p × Fin p)).filter
          (fun x => x.1 < x.2 ∧ b x.1 ≠ b x.2)).card := by
    dsimp [pairs]
    rw [Finset.sum_filter, Finset.card_eq_sum_ones, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro x hx
    by_cases hlt : x.1 < x.2 <;> by_cases hdiff : b x.1 ≠ b x.2 <;>
      simp [hlt, hdiff]
  have hcard := card_unordered_bool_diff p b
  let trueRows : Finset (Fin p) := Finset.univ.filter (fun i => b i = true)
  let falseRows : Finset (Fin p) := Finset.univ.filter (fun i => b i = false)
  have hcounts : trueRows.card + falseRows.card = p := by
    have h := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin p))) (fun i => b i = true)
    simpa [trueRows, falseRows] using h
  have hfalse : falseRows.card = p - trueRows.card := by omega
  change (∑ x ∈ pairs, if b x.1 ≠ b x.2 then 1 else 0) =
    trueRows.card * (p - trueRows.card)
  have hcard' :
      ((Finset.univ : Finset (Fin p × Fin p)).filter
          (fun x => x.1 < x.2 ∧ b x.1 ≠ b x.2)).card =
        trueRows.card * falseRows.card := by
    simpa [trueRows, falseRows] using hcard
  rw [hsum, hcard', hfalse]

end MathlibPlus.Combinatorics
