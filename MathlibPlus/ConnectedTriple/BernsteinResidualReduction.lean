-- UNVERIFIED (native-decide): submitted but not kernel-verified, so it is not built and MathlibPlus.lean does not import it. See unverified.txt.
import MathlibPlus.Open.ConnectedTriple.BernsteinPattern
import MathlibPlus.Open.ConnectedTriple.ScaledEdgeResidual

open scoped BigOperators

namespace MathlibPlus.ConnectedTriple

open MathlibPlus.Open.ConnectedTriple

/-- The coefficient-pattern certificate implies the scaled-edge residual certificate.
This is the one-way extraction of the positive off-face coefficients. -/
theorem bernsteinCoefficientPattern_implies_scaledEdgeResidualDecomposition :
    bernsteinCoefficientPattern → scaledEdgeResidualDecomposition := by
  intro h
  dsimp [bernsteinCoefficientPattern] at h
  dsimp [scaledEdgeResidualDecomposition]
  rcases h with ⟨P, β, hscale, hsymm, hexpand, hneg, hpos, hcountpos, hcountneg⟩
  let R : ℝ → ℝ → ℝ → ℝ := fun r s t => P r s t - (1 - 16 * t) ^ 7 * P r s 0
  let β' : Fin 8 → Fin 8 → Fin 8 → ℝ := fun i j k => if k = 0 then 0 else β i j k
  let basis : ℝ → ℝ → Fin 8 → ℝ := fun upper x i =>
    (Nat.choose 7 i.1 : ℝ) * (x / upper) ^ i.1 *
      (1 - x / upper) ^ (7 - i.1)
  have hexpand' : ∀ (r s t : ℝ),
      0 ≤ r → r ≤ 1 / 4 → 0 ≤ s → s ≤ 1 / 9 →
      0 ≤ t → t ≤ 1 / 16 →
      P r s t = ∑ i, ∑ j, ∑ k,
        β i j k * basis (1 / 4) r i * basis (1 / 9) s j * basis (1 / 16) t k := by
    intro r s t hr0 hr1 hs0 hs1 ht0 ht1
    simpa [basis] using hexpand r s t hr0 hr1 hs0 hs1 ht0 ht1
  have hβzero : ∀ i j k, β' i j k = 0 ↔ k = 0 := by
    intro i j k
    by_cases hk : k = 0
    · simp [β', hk]
    · simp only [β', hk, if_false]
      constructor
      · intro hb
        have hβ : 0 < β i j k := (hpos i j k).2 (by
          intro hbad
          exact hk hbad.2.1)
        linarith
      · intro hk0
        exact False.elim hk0
  have hβpos : ∀ i j k, 0 < β' i j k ↔ ¬ k = 0 := by
    intro i j k
    by_cases hk : k = 0
    · simp [β', hk]
    · simp only [β', hk, if_false]
      constructor
      · intro hb
        simp
      · intro _
        exact hpos i j k |>.2 (by
          intro hbad
          exact hk hbad.2.1)
  have hR_expand : ∀ (r s t : ℝ),
      0 ≤ r → r ≤ 1 / 4 → 0 ≤ s → s ≤ 1 / 9 →
      0 ≤ t → t ≤ 1 / 16 →
      R r s t = ∑ i, ∑ j, ∑ k,
        β' i j k * basis (1 / 4) r i * basis (1 / 9) s j * basis (1 / 16) t k := by
    intro r s t hr0 hr1 hs0 hs1 ht0 ht1
    have h₁ := hexpand' r s t hr0 hr1 hs0 hs1 ht0 ht1
    have h₀ := hexpand' r s 0 hr0 hr1 hs0 hs1 (by norm_num) (by norm_num)
    dsimp [R]
    rw [h₁, h₀]
    have hbasis : ∀ k : Fin 8,
        basis (1 / 16) t k - (1 - 16 * t) ^ 7 * basis (1 / 16) 0 k =
          (if k = 0 then 0 else 1) * basis (1 / 16) t k := by
      intro k
      fin_cases k <;> simp [basis] <;> ring
    have hmul (c : ℝ) (f : Fin 8 → Fin 8 → Fin 8 → ℝ) :
        c * (∑ i, ∑ j, ∑ k, f i j k) =
          ∑ i, ∑ j, ∑ k, c * f i j k := by
      rw [Finset.mul_sum (s := Finset.univ)]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mul_sum (s := Finset.univ)]
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.mul_sum (s := Finset.univ)]
    have hsub (f g : Fin 8 → Fin 8 → Fin 8 → ℝ) :
        (∑ i, ∑ j, ∑ k, f i j k) - (∑ i, ∑ j, ∑ k, g i j k) =
          ∑ i, ∑ j, ∑ k, (f i j k - g i j k) := by
      symm
      calc
        (∑ i, ∑ j, ∑ k, (f i j k - g i j k)) =
            ∑ i, ∑ j, ((∑ k, f i j k) - (∑ k, g i j k)) := by
          apply Finset.sum_congr rfl
          intro i hi
          apply Finset.sum_congr rfl
          intro j hj
          exact (Finset.sum_sub_distrib (s := Finset.univ)
            (fun k => f i j k) (fun k => g i j k))
        _ = ∑ i, ((∑ j, ∑ k, f i j k) - (∑ j, ∑ k, g i j k)) := by
          apply Finset.sum_congr rfl
          intro i hi
          exact (Finset.sum_sub_distrib (s := Finset.univ)
            (fun j => ∑ k, f i j k) (fun j => ∑ k, g i j k))
        _ = (∑ i, ∑ j, ∑ k, f i j k) - (∑ i, ∑ j, ∑ k, g i j k) :=
          (Finset.sum_sub_distrib (s := Finset.univ)
            (fun i => ∑ j, ∑ k, f i j k) (fun i => ∑ j, ∑ k, g i j k))
    calc
      (∑ i, ∑ j, ∑ k,
          β i j k * basis (1 / 4) r i * basis (1 / 9) s j * basis (1 / 16) t k) -
          (1 - 16 * t) ^ 7 *
            ∑ i, ∑ j, ∑ k,
              β i j k * basis (1 / 4) r i * basis (1 / 9) s j * basis (1 / 16) 0 k =
        ∑ i, ∑ j, ∑ k,
          (β i j k * basis (1 / 4) r i * basis (1 / 9) s j * basis (1 / 16) t k -
            (1 - 16 * t) ^ 7 *
              (β i j k * basis (1 / 4) r i * basis (1 / 9) s j * basis (1 / 16) 0 k)) := by
            rw [hmul]
            rw [hsub]
      _ = ∑ i, ∑ j, ∑ k,
          β' i j k * basis (1 / 4) r i * basis (1 / 9) s j * basis (1 / 16) t k := by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        apply Finset.sum_congr rfl
        intro k hk
        calc
          β i j k * basis (1 / 4) r i * basis (1 / 9) s j * basis (1 / 16) t k -
              (1 - 16 * t) ^ 7 *
                (β i j k * basis (1 / 4) r i * basis (1 / 9) s j * basis (1 / 16) 0 k) =
              (β i j k * basis (1 / 4) r i * basis (1 / 9) s j) *
                (basis (1 / 16) t k - (1 - 16 * t) ^ 7 * basis (1 / 16) 0 k) := by ring
          _ = β' i j k * basis (1 / 4) r i * basis (1 / 9) s j * basis (1 / 16) t k := by
            rw [hbasis k]
            by_cases hk0 : k = 0 <;> simp [β', hk0]
  refine ⟨P, R, β', hscale, hsymm, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro r s t
    dsimp [R]
    ring
  · intro r s t hr0 hr1 hs0 hs1 ht0 ht1
    exact hR_expand r s t hr0 hr1 hs0 hs1 ht0 ht1
  · intro i j k
    exact hβzero i j k
  · intro i j k
    exact hβpos i j k
  · have hext :
        (Finset.univ.filter (fun x : Fin 8 × Fin 8 × Fin 8 =>
          β' x.1 x.2.1 x.2.2 = 0)) =
        (Finset.univ.filter (fun x : Fin 8 × Fin 8 × Fin 8 =>
          x.2.2 = 0)) := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hβzero x.1 x.2.1 x.2.2
    rw [hext]
    native_decide
  · have hext :
        (Finset.univ.filter (fun x : Fin 8 × Fin 8 × Fin 8 =>
          0 < β' x.1 x.2.1 x.2.2)) =
        (Finset.univ.filter (fun x : Fin 8 × Fin 8 × Fin 8 =>
          ¬ x.2.2 = 0)) := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hβpos x.1 x.2.1 x.2.2
    rw [hext]
    native_decide
  · intro r s t hr0 hr1 hs0 hs1 ht0 ht1
    have hbasis_nonneg (upper x : ℝ) (hupper : 0 < upper)
        (hx0 : 0 ≤ x) (hx1 : x ≤ upper) (i : Fin 8) :
        0 ≤ basis upper x i := by
      have hratio0 : 0 ≤ x / upper := div_nonneg hx0 (le_of_lt hupper)
      have hratio1 : x / upper ≤ 1 := by
        apply (div_le_iff₀ hupper).2
        linarith
      dsimp [basis]
      exact mul_nonneg
        (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hratio0 _))
        (pow_nonneg (by linarith) _)
    have hbasis_anchor (upper x : ℝ) (hupper : 0 < upper)
        (hx0 : 0 ≤ x) (hx1 : x ≤ upper) :
        0 < basis upper x (if x = 0 then 0 else 7) := by
      by_cases hx : x = 0
      · simp [hx, basis]
      · have hxpos : 0 < x := lt_of_le_of_ne hx0 (Ne.symm hx)
        have hratio : 0 < x / upper := div_pos hxpos hupper
        simp [hx, basis]
        positivity
    have hβnonneg (i j k : Fin 8) : 0 ≤ β' i j k := by
      by_cases hk : k = 0
      · simp [β', hk]
      · exact le_of_lt ((hβpos i j k).2 hk)
    have hterm_nonneg (i j k : Fin 8) :
        0 ≤ β' i j k * basis (1 / 4) r i * basis (1 / 9) s j * basis (1 / 16) t k := by
      exact mul_nonneg
        (mul_nonneg
          (mul_nonneg (hβnonneg i j k)
            (hbasis_nonneg (1 / 4) r (by norm_num) hr0 (by linarith) i))
          (hbasis_nonneg (1 / 9) s (by norm_num) hs0 (by linarith) j))
        (hbasis_nonneg (1 / 16) t (by norm_num) (le_of_lt ht0) (by linarith) k)
    let i₀ : Fin 8 := if r = 0 then 0 else 7
    let j₀ : Fin 8 := if s = 0 then 0 else 7
    have hbi : 0 < basis (1 / 4) r i₀ := by
      simpa [i₀] using hbasis_anchor (1 / 4) r (by norm_num) hr0 (by linarith)
    have hbj : 0 < basis (1 / 9) s j₀ := by
      simpa [j₀] using hbasis_anchor (1 / 9) s (by norm_num) hs0 (by linarith)
    have hbk : 0 < basis (1 / 16) t (7 : Fin 8) := by
      have htanchor := hbasis_anchor (1 / 16) t (by norm_num) (le_of_lt ht0) (by linarith)
      simpa [ne_of_gt ht0] using htanchor
    have hβ7 : 0 < β' i₀ j₀ (7 : Fin 8) :=
      (hβpos i₀ j₀ (7 : Fin 8)).2 (by decide)
    have hterm_pos :
        0 < β' i₀ j₀ (7 : Fin 8) * basis (1 / 4) r i₀ *
          basis (1 / 9) s j₀ * basis (1 / 16) t (7 : Fin 8) := by
      exact mul_pos (mul_pos (mul_pos hβ7 hbi) hbj) hbk
    have hK_nonneg (i j : Fin 8) :
        0 ≤ ∑ k, β' i j k * basis (1 / 4) r i * basis (1 / 9) s j * basis (1 / 16) t k := by
      exact Finset.sum_nonneg (fun k hk => hterm_nonneg i j k)
    have hJ_nonneg (i : Fin 8) :
        0 ≤ ∑ j, ∑ k,
          β' i j k * basis (1 / 4) r i * basis (1 / 9) s j * basis (1 / 16) t k := by
      exact Finset.sum_nonneg (fun j hj => hK_nonneg i j)
    have houter_nonneg :
        0 ≤ ∑ i, ∑ j, ∑ k,
          β' i j k * basis (1 / 4) r i * basis (1 / 9) s j * basis (1 / 16) t k := by
      exact Finset.sum_nonneg (fun i hi => hJ_nonneg i)
    have hK_pos :
        0 < ∑ k,
          β' i₀ j₀ k * basis (1 / 4) r i₀ * basis (1 / 9) s j₀ * basis (1 / 16) t k := by
      exact Finset.sum_pos' (fun k hk => hterm_nonneg i₀ j₀ k)
        ⟨(7 : Fin 8), by simp, hterm_pos⟩
    have hJ_pos :
        0 < ∑ j, ∑ k,
          β' i₀ j k * basis (1 / 4) r i₀ * basis (1 / 9) s j * basis (1 / 16) t k := by
      exact Finset.sum_pos' (fun j hj => hK_nonneg i₀ j)
        ⟨j₀, by simp, hK_pos⟩
    have houter_pos :
        0 < ∑ i, ∑ j, ∑ k,
          β' i j k * basis (1 / 4) r i * basis (1 / 9) s j * basis (1 / 16) t k := by
      exact Finset.sum_pos' (fun i hi => hJ_nonneg i)
        ⟨i₀, by simp, hJ_pos⟩
    rw [hR_expand r s t hr0 hr1 hs0 hs1 (le_of_lt ht0) ht1]
    exact houter_pos

end MathlibPlus.ConnectedTriple
