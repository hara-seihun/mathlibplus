import Mathlib

namespace MathlibPlus.NumberTheory.Claim9313

/--
A nonconstant monic polynomial over the integers with nonzero constant term
cannot have all of its complex roots in the open unit disk.  The proof keeps
multiplicities through `Polynomial.roots`; the integer constant term then has
norm at least one, while the product of the root norms is strictly less than
one.
-/
theorem monicIntegralUnitDiskFactorObstruction_claim9313
    (p : Polynomial ℤ)
    (hmonic : p.Monic)
    (hdegree : 0 < p.natDegree)
    (hconstant : p.coeff 0 ≠ 0)
    (hroots : ∀ z ∈ (p.map (Int.castRingHom ℂ)).roots, ‖z‖ < 1) :
    False := by
  let P : Polynomial ℂ := p.map (Int.castRingHom ℂ)
  have hPsplit : P.Splits := IsAlgClosed.splits P
  have hPmonic : P.Monic := by
    simpa [P] using hmonic.map (Int.castRingHom ℂ)
  have hPdegree : P.natDegree = p.natDegree := by
    simpa [P] using (Polynomial.natDegree_map_eq_of_injective
      (f := Int.castRingHom ℂ) (Int.cast_injective (α := ℂ)) p)
  have hroots_nonempty : P.roots ≠ 0 := by
    intro hzero
    have hPdegree_zero : P.natDegree = 0 := by
      rw [hPsplit.natDegree_eq_card_roots, hzero]
      rfl
    exact (Nat.ne_of_gt hdegree) (hPdegree ▸ hPdegree_zero)
  have hprod_nonneg : ∀ s : Multiset ℂ, 0 ≤ (s.map norm).prod := by
    intro s
    induction s using Multiset.induction_on with
    | empty => simp
    | @cons z s ih =>
      simp only [Multiset.map_cons, Multiset.prod_cons]
      exact mul_nonneg (norm_nonneg z) ih
  have hprod_lt_one : ∀ s : Multiset ℂ,
      (∀ z ∈ s, ‖z‖ < 1) → s ≠ 0 → (s.map norm).prod < 1 := by
    intro s
    induction s using Multiset.induction_on with
    | empty => simp
    | @cons z s ih =>
      intro hall hne
      have hz : ‖z‖ < 1 := hall z (by simp)
      by_cases hs : s = 0
      · simp [hs, hz]
      · have htail := ih (fun y hy => hall y (by simp [hy])) hs
        simpa [Multiset.map_cons, Multiset.prod_cons] using
          mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg z) hz
            htail.le
  have hprod_norm_eq : ‖P.roots.prod‖ = (P.roots.map norm).prod := by
    induction P.roots using Multiset.induction_on with
    | empty => simp
    | @cons z s ih => simp [ih]
  have hprod_norm_lt : ‖P.roots.prod‖ < 1 := by
    rw [hprod_norm_eq]
    exact hprod_lt_one P.roots (by
      intro z hz
      exact hroots z (by simpa [P] using hz)) hroots_nonempty
  have hcoeff_eq : P.coeff 0 = (-1 : ℂ) ^ P.natDegree * P.roots.prod :=
    hPsplit.coeff_zero_eq_prod_roots_of_monic hPmonic
  have hcoeff_norm_lt : ‖P.coeff 0‖ < 1 := by
    rw [hcoeff_eq, norm_mul, norm_pow, norm_neg, norm_one]
    simpa using hprod_norm_lt
  have hcoeff_norm_ge : (1 : ℝ) ≤ ‖P.coeff 0‖ := by
    have hint : (1 : ℝ) ≤ |p.coeff 0| := by
      exact_mod_cast Int.one_le_abs hconstant
    simpa [P, Complex.norm_intCast, Int.cast_abs] using hint
  linarith

end MathlibPlus.NumberTheory.Claim9313
