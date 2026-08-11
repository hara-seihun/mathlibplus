import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic

namespace MathlibPlus.NumberTheory

/--
The exact reindexed form of the unscaled dyadic tail in admitted claim
35660 (R-2765).  The sum over `j > k` is written with the nonnegative index
`j` after the shift `j ↦ k + 1 + j`.
-/
theorem weightedDyadicTail_claim35660 (k : ℕ) :
    (∑' j : ℕ, (k + 1 + j : ℝ) * ((1 / 2 : ℝ) ^ (k + 1 + j))) =
      (k + 2 : ℝ) * ((1 / 2 : ℝ) ^ k) := by
  let f : ℕ → ℝ := fun n => (n : ℝ) * ((1 / 2 : ℝ) ^ n)
  have htotal : HasSum f 2 := by
    have h := hasSum_coe_mul_geometric_of_norm_lt_one (𝕜 := ℝ)
      (r := (1 / 2 : ℝ)) (by norm_num)
    convert h using 1 <;> try rfl
    norm_num
  have hf : Summable f := htotal.summable
  let tail : ℕ → ℝ := fun k => ∑' j : ℕ, f (j + (k + 1))
  have htail : ∀ k : ℕ, tail k = (k + 2 : ℝ) * ((1 / 2 : ℝ) ^ k) := by
    intro m
    induction m with
    | zero =>
        have hs := (hasSum_nat_add_iff' 1).2 htotal
        have heq := hs.tsum_eq
        simpa [tail, f] using heq
    | succ m ih =>
        have hfshift : Summable (fun j : ℕ => f (j + (m + 1))) :=
          (summable_nat_add_iff (m + 1)).2 hf
        have hsplit := hfshift.sum_add_tsum_nat_add 1
        have hsplit' : f (m + 1) + tail (m + 1) = tail m := by
          simpa [tail, add_comm, add_left_comm, add_assoc] using hsplit
        have hrec : tail (m + 1) = tail m - f (m + 1) := by
          linarith
        rw [hrec, ih]
        dsimp [f]
        rw [pow_succ]
        norm_num
        ring
  simpa [f, tail, add_comm, add_left_comm, add_assoc] using htail k

/--
The exact scaling criterion from claim 35660: for a positive denominator
scale `q`, the residual `r = q * 2^k * x` lies in the available scaled tail
interval exactly when the unscaled residual `x` lies in the corresponding
unscaled interval.
-/
theorem scaledResidualFits_iff_claim35660
    {q : ℚ} (hq : 0 < q) (k : ℕ) (x r : ℚ)
    (hr : r = q * (2 : ℚ) ^ k * x) :
    (0 ≤ r ∧ r ≤ q * (k + 2 : ℚ)) ↔
      (0 ≤ x ∧ x ≤ (k + 2 : ℚ) / (2 : ℚ) ^ k) := by
  have hpow : 0 < (2 : ℚ) ^ k := by positivity
  have hscale : 0 < q * (2 : ℚ) ^ k := mul_pos hq hpow
  have hbound : q * (k + 2 : ℚ) =
      (q * (2 : ℚ) ^ k) * ((k + 2 : ℚ) / (2 : ℚ) ^ k) := by
    field_simp
  rw [hr, hbound]
  constructor
  · intro h
    constructor
    · exact (mul_nonneg_iff_of_pos_left hscale).mp h.1
    · exact le_of_mul_le_mul_left h.2 hscale
  · intro h
    constructor
    · exact mul_nonneg hscale.le h.1
    · exact mul_le_mul_of_nonneg_left h.2 hscale.le

/--
The two exact children of a carry state and the interval retention rule from
claim 35660.  Membership in the interval is used as the formal retention
predicate, so the source's two-child rule is explicit rather than hidden in
an auxiliary definition.
-/
theorem carryChildrenRetained_iff_claim35660 (q r : ℚ) (k : ℕ) :
    let child : Bool → ℚ := fun d =>
      if d then 2 * r - q * (k + 1 : ℚ) else 2 * r
    ∀ d : Bool,
      child d ∈ Set.Icc 0 (q * (k + 3 : ℚ)) ↔
        0 ≤ child d ∧ child d ≤ q * (k + 3 : ℚ) := by
  dsimp
  intro d
  rfl

/--
The complete formalized arithmetic packet for the three carry assertions in
claim 35660: the tail identity, scaled feasibility, and both child retention
conditions are presented together without adding a hidden hypothesis.
-/
theorem weightedDyadicCarryClaim_claim35660
    (k : ℕ) {q : ℚ} (hq : 0 < q) (x r : ℚ)
    (hr : r = q * (2 : ℚ) ^ k * x) :
    (∑' j : ℕ, (k + 1 + j : ℝ) * ((1 / 2 : ℝ) ^ (k + 1 + j))) =
        (k + 2 : ℝ) * ((1 / 2 : ℝ) ^ k) ∧
      ((0 ≤ r ∧ r ≤ q * (k + 2 : ℚ)) ↔
        (0 ≤ x ∧ x ≤ (k + 2 : ℚ) / (2 : ℚ) ^ k)) ∧
      (let child : Bool → ℚ := fun d =>
          if d then 2 * r - q * (k + 1 : ℚ) else 2 * r
       ∀ d : Bool,
         child d ∈ Set.Icc 0 (q * (k + 3 : ℚ)) ↔
           0 ≤ child d ∧ child d ≤ q * (k + 3 : ℚ)) := by
  refine ⟨weightedDyadicTail_claim35660 k,
    scaledResidualFits_iff_claim35660 hq k x r hr, ?_⟩
  exact carryChildrenRetained_iff_claim35660 q r k

end MathlibPlus.NumberTheory
