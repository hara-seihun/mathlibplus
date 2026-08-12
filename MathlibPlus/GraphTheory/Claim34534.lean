import Mathlib

namespace MathlibPlus.GraphTheory

/-- Claim 34534: under the degree-four/degree-five alternative outside `S`,
the curvature identity bounds the degree-five exceptional set and the enlarged
exceptional set. -/
theorem degreeFiveCountBound_claim34534
    {V : Type*} [Fintype V] [DecidableEq V]
    (S : Finset V) (deg : V → ℕ) (c b E : ℕ)
    (hdeg : ∀ v, v ∉ S → deg v = 4 ∨ deg v = 5)
    (hcurv : ∑ v : V, ((4 : ℤ) - (deg v : ℤ)) = (4 * c + b + E : ℤ))
    (hS : (S.card : ℤ) ≤ (c + b + 5 * E : ℤ)) :
    let U : Finset V := Finset.univ \ S
    let T₅ : Finset V := U.filter (fun v => deg v = 5)
    let B : Finset V := S ∪ T₅
    T₅.card ≤ 4 * S.card ∧
      B.card ≤ 5 * (c + b + 5 * E) := by
  classical
  let U : Finset V := Finset.univ \ S
  let T₅ : Finset V := U.filter (fun v => deg v = 5)
  let T₄ : Finset V := U.filter (fun v => deg v = 4)
  let B : Finset V := S ∪ T₅
  have hU : U = T₄ ∪ T₅ := by
    ext v
    simp only [U, T₄, T₅, Finset.mem_sdiff, Finset.mem_univ, true_and,
      Finset.mem_union, Finset.mem_filter]
    by_cases hv : v ∈ S
    · simp [hv]
    · have h := hdeg v hv
      rcases h with h | h
      · simp [hv, h]
      · simp [hv, h]
  have hdisj : Disjoint T₄ T₅ := by
    rw [Finset.disjoint_left]
    intro v hv4 hv5
    simp only [T₄, T₅, Finset.mem_filter] at hv4 hv5
    omega
  have hU_sum : (∑ v ∈ U, ((4 : ℤ) - (deg v : ℤ))) = -(T₅.card : ℤ) := by
    rw [hU, Finset.sum_union hdisj]
    have h4sum : (∑ v ∈ T₄, ((4 : ℤ) - (deg v : ℤ))) = 0 := by
      apply Finset.sum_eq_zero
      intro v hv
      simp only [T₄, Finset.mem_filter] at hv
      omega
    have h5sum : (∑ v ∈ T₅, ((4 : ℤ) - (deg v : ℤ))) = -(T₅.card : ℤ) := by
      calc
        (∑ v ∈ T₅, ((4 : ℤ) - (deg v : ℤ))) =
            ∑ v ∈ T₅, (-1 : ℤ) := by
              apply Finset.sum_congr rfl
              intro v hv
              simp only [T₅, Finset.mem_filter] at hv
              omega
        _ = -(T₅.card : ℤ) := by
          rw [Finset.sum_const]
          simp
    rw [h4sum, h5sum, zero_add]
  have hunion : (Finset.univ : Finset V) = S ∪ U := by
    ext v
    simp [U]
  have hdisjSU : Disjoint S U := by
    rw [Finset.disjoint_left]
    intro v hvS hvU
    simp only [U, Finset.mem_sdiff] at hvU
    exact hvU.2 hvS
  have hsplit :
      ∑ v : V, ((4 : ℤ) - (deg v : ℤ)) =
        (∑ v ∈ S, ((4 : ℤ) - (deg v : ℤ))) +
          ∑ v ∈ U, ((4 : ℤ) - (deg v : ℤ)) := by
    rw [← Finset.sum_union hdisjSU, ← hunion]
  have hSupper :
      (∑ v ∈ S, ((4 : ℤ) - (deg v : ℤ))) ≤ (4 * S.card : ℤ) := by
    calc
      (∑ v ∈ S, ((4 : ℤ) - (deg v : ℤ))) ≤ ∑ _v ∈ S, (4 : ℤ) := by
        apply Finset.sum_le_sum
        intro v hv
        have hnonneg : (0 : ℤ) ≤ (deg v : ℤ) := by positivity
        omega
      _ = (4 * S.card : ℤ) := by simp; ring
  have hT : (T₅.card : ℤ) ≤ 4 * S.card := by
    rw [hcurv] at hsplit
    rw [hU_sum] at hsplit
    linarith
  have hTnat : T₅.card ≤ 4 * S.card := by
    exact_mod_cast hT
  constructor
  · exact hTnat
  · have hdisjST : Disjoint S T₅ := by
      rw [Finset.disjoint_left]
      intro v hvS hvT
      simp only [T₅, U, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ,
        true_and] at hvT
      exact hvT.1 hvS
    have hBcard : B.card = S.card + T₅.card := by
      simpa [B] using Finset.card_union_of_disjoint hdisjST
    have hBnat : B.card ≤ 5 * S.card := by
      rw [hBcard]
      omega
    have hSnat : S.card ≤ c + b + 5 * E := by
      exact_mod_cast hS
    calc
      B.card ≤ 5 * S.card := hBnat
      _ ≤ 5 * (c + b + 5 * E) := by omega

end MathlibPlus.GraphTheory
